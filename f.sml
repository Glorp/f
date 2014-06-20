fun curry f a b = f (a, b)
fun uncurry f (a, b) = f a b
fun flip f a b = f b a
fun apply f a = f a

fun omap opt f = case opt of
                     NONE   => NONE
                   | SOME x => SOME (f x)
fun obnd opt f = case opt of
                     NONE   => NONE
                   | SOME x => f x
fun oor opt f = case opt of
                    NONE => f ()
                  | x    => x

datatype term = Lam of string * term * term
              | TLam of string * term
              | Pi of string * term
              | Arr of term * term
	      | App of term * term
	      | Var of string
 
datatype def = Define of string * term
 
datatype stmt = Term of term
              | Def of def
              | Undef of string
 
datatype exec = Reduction of (term * term)
              | Rename of (string * term * string * term)
              | Normal of term
              | Other of string

fun pstring s = "(" ^ s ^")"
                                     
fun termstr (Lam (p, ty, b))          = "#l(" ^ p ^ " : " ^ termstr ty ^ ")." ^ termstr b
  | termstr (TLam (p, b))             = "#L" ^ p ^ "." ^ termstr b 
  | termstr (Pi (p, t))               = "#P" ^ p ^ "." ^ termstr t
  | termstr (Arr (f, t))                 = arrstr f ^ " -> " ^ termstr t
  | termstr (App (Lam (p, ty, b), a)) = pstring (termstr (Lam (p, ty, b))) ^ " " ^ argstring a
  | termstr (App (TLam (p, b), a))    = pstring (termstr (TLam (p, b))) ^ " " ^ argstring a
  | termstr (App (f, a))              = termstr f ^ " " ^ argstring a
  | termstr (Var s)                   = s
and argstring (Var s) = s
  | argstring t       = pstring (termstr t)
and arrstr (Var s) = s
  | arrstr t       =  pstring (termstr t)
 
fun lam p t b = Lam (p, t, b)
val tlam = curry TLam
val pi = curry Pi
val app = curry App
val arr = curry Arr
 
fun findTerm pred t =
    let fun findBin ctor t1 t2 res = oor (find t1 (flip ctor t2 :: res))
                                         (fn _ => find t2 (ctor t1  :: res))
        and find t res      =
            case (pred t) of
                SOME x => SOME (x, res)
              | NONE   => (case t of
                               Lam (p, t, b) => findBin (fn t => fn b => Lam (p, t, b)) t b res
                             | App (f, a)    => findBin app f a res
                             | Arr (t, f)    => findBin arr t f res
                             | TLam (p, b)   => find b (tlam p :: res)
                             | Pi (p, b)     => find b (pi p :: res)
                             | Var _ => NONE)
    in find t []
    end
 
fun fterm t tz = foldl (uncurry apply) t tz
 
fun reducible (App (Lam (p, t, b), a)) = SOME ((p, b, a), fn (p, b, a) => (App (Lam (p, t, b), a)))
  | reducible (App (TLam (p, b), a))   = SOME ((p, b, a), fn (p, b, a) => (App (TLam (p, b), a)))
  | reducible _                        = NONE
 
 
fun subst t s (App (f, a))     = App (subst t s f, subst t s a)
  | subst t s (Arr (t1, t2))   = Arr (subst t s t1, subst t s t2)
  | subst t s (Lam (p, ty, b)) = if p = s then Lam (p, subst t s ty, b)
                                 else Lam (p, subst t s ty, subst t s b)
  | subst t s (TLam (p, b))    = if p = s then TLam (p, b)
                                 else TLam (p, subst t s b)
  | subst t s (Pi (p, b))      = if p = s then Pi (p, b)
                                 else Pi (p, subst t s b)
  | subst t s (Var v)          = if v = s then t
                                 else Var v
 
val renameDefs =
    let fun renameDef ((Define (ds, dt)), trm) = subst dt ds trm
    in foldr renameDef
    end

structure SSet = ListSetFn (struct
                             type ord_key = string
                             val compare = String.compare
                             end)
 
fun freeIds (Var s) env         = if SSet.member (env, s) then SSet.empty
                                  else SSet.singleton s
  | freeIds (App (f, a)) env    = SSet.union (freeIds f env, freeIds a env)
  | freeIds (Arr (t1, t2)) env  = SSet.union (freeIds t1 env, freeIds t2 env)
  | freeIds (Lam (p, t, b)) env = SSet.union (freeIds b (SSet.add (env, p)), freeIds t env)
  | freeIds (TLam (p, b)) env   = freeIds b (SSet.add (env, p))
  | freeIds (Pi (p, b)) env     = freeIds b (SSet.add (env, p))
 
fun allIds (Var s)          = SSet.singleton s
  | allIds (App (f, a))     = SSet.union (allIds f, allIds a)
  | allIds (Arr (f, a))     = SSet.union (allIds f, allIds a)
  | allIds (Lam (p, t, b))  = SSet.add (SSet.union (allIds b, allIds t), p)
  | allIds (TLam (p, b))    = SSet.add (allIds b, p)
  | allIds (Pi (p, b))      = SSet.add (allIds b, p)
 
fun uniqueId t s =
    let val ids = allIds t
        fun uniq n = let val newId = s ^ Int.toString n
                     in if SSet.member (ids, newId) then uniq (n + 1)
                        else newId
                     end
    in uniq 2
    end
 
fun conflict param body arg =
    let val ids = (freeIds arg SSet.empty)
        fun conf t poss res =
            let fun binderConf p b f =
		    if param = p then NONE
                    else if SSet.member (ids, p) then conf b (SOME (p, b, f, res)) (curry f p :: res)
                    else conf b poss (curry f p :: res)
                fun binConf t1 t2 f = oor (conf t1 poss (flip app t2 :: res))
                                          (fn _ => conf t2 poss (app t1 :: res))
            in case t of
                   Lam (p, t, b) => oor (binderConf p b (fn (p, b) => Lam (p, t, b)))
                                        (fn _ => conf t poss ((fn t => Lam (p, t, b)) :: res))
                 | TLam (p, b)   => binderConf p b TLam
                 | Pi (p, b)     => binderConf p b Pi
                 | App (f, a)    => binConf f a app
                 | Arr (f, t)    => binConf f t arr
                 | Var s         => if s = param then poss
                                    else NONE
            end
    in if SSet.isEmpty ids then NONE
       else conf body NONE []
    end
 
fun reduceRename t =
    let fun rename p b f tz = let val s = uniqueId t p
                              in Rename (p, t, s, fterm (f (s, (subst (Var s) p b))) tz)
                              end
        fun reduceRename0 (((rp, rb, ra), rfun), rtz) =
		case conflict rp rb ra of
		    NONE                     => Reduction (t, fterm (subst ra rp rb) rtz)
		  | SOME (cp, cb, cfun, ctz) =>
                    rename cp cb cfun (List.concat [ctz, [fn b => rfun (rp, b, ra)], rtz])
    in case findTerm reducible t of
           SOME red => reduceRename0 red
         | NONE     => Normal t
    end

datatype ctxi = Type of string | Annot of string * term

fun lookup s []                   = NONE
  | lookup s (Type n :: xs)       = if s = n then SOME (Type n)
                                    else lookup s xs
  | lookup s (Annot (n, t) :: xs) = if s = n then SOME (Annot (n, t))
                                    else lookup s xs

fun substVery param body arg t =
    case conflict param body arg of
        NONE                     => subst arg param body
      | SOME (cp, cb, cfun, ctz) =>
        let val s = uniqueId t cp
        in substVery param (fterm (cfun (s, (subst (Var s) cp cb))) ctz) arg t
        end

fun typeof outert ctx trm =
    case trm of
        Var s => (case lookup s ctx of
                      SOME (Annot (_, t)) => SOME t
                    | _                   => NONE)
      | Lam (p, t, b) => if not (isType outert ctx t) then NONE
                         else omap (typeof outert (Annot (p, t) :: ctx) b)
                                   (fn rt => Arr (t, rt))
      | TLam (p, b)   => let val ids = freeIds b SSet.empty
                             fun isConflict s =
                                 (case lookup s ctx of
                                     SOME (Annot (_, t)) => SSet.member (freeIds t SSet.empty, p)
                                  | _                    => false)
                             fun renameTLam _ = let val s = uniqueId outert p
                                                in TLam (s, subst (Var s) p b)
                                                end
                         in if SSet.exists isConflict ids then typeof outert ctx (renameTLam ())
                            else omap (typeof outert (Type p :: ctx) b)
                                      (fn rt => Pi (p, rt))
                         end
      | App (f, a)    => (case typeof outert ctx f of
                              SOME (Arr (f, t)) => obnd (typeof outert ctx a)
                                                        (fn at => if sameType outert ctx ctx f at then SOME t
                                                                  else NONE)
                            | SOME (Pi (p, b))  => if isType outert ctx a then SOME (substVery p b a outert)
                                                   else NONE
                            | _                 => NONE)
      | _             => NONE
and isType outert ctx trm =
    case trm of
        Var s              => (case lookup s ctx of
                                   SOME (Type _) => true
                                 | _             => false)
      | Arr (f, t)         => isType outert ctx f andalso isType outert ctx t
      | Pi (p, b)          => isType outert ((Type p) :: ctx) b
      | App (f, a)         => (case typeof outert ctx f of
                                   SOME (Pi (_, _)) => isType outert ctx a
                                 | _                => false)
      | _                  => false
and sameType outert actx bctx at bt =
    let fun sameStr (Type a :: xs) (Type b :: ys) s1 s2 =
            if a = s1 andalso b = s2 then true
            else if a = s1 orelse b = s2 then false
            else sameStr xs ys s1 s2
          | sameStr (Type a :: xs) (_ :: ys) s1 s2 = if a = s1 then false
                                                     else sameStr xs ys s1 s2
          | sameStr (_ :: xs) (Type b :: ys) s1 s2 = if b = s2 then false
                                                     else sameStr xs ys s1 s2
          | sameStr (x :: xs) (y :: ys) s1 s2 = sameStr xs ys s1 s2
          | sameStr _ _ s1 s2 = false
        fun same (Var s1) (Var s2) = sameStr actx bctx s1 s2
          | same (Arr (f1, t1)) (Arr (f2, t2)) =
            same f1 f2 andalso same t1 t2
          | same (Pi (p1, b1)) (Pi (p2, b2)) = 
            sameType outert (Type p1 :: actx) (Type p2 :: bctx) b1 b2
          | same _ _  = false
    in same at bt
    end

                                  
                                  
fun seperator c = c = #"."
                  orelse c = #"("
                  orelse c = #")"
                  orelse c = #"#"
                  orelse Char.isSpace c

fun readChar c (s, p, m) = if m > p andalso String.sub (s, p) = c then SOME (s, p + 1, m)
                           else NONE

fun readWhites (s, p, m) = 
    if m > p andalso Char.isSpace (String.sub (s, p)) then readWhites (s, p + 1, m)
    else (s, p, m)

fun atEnd str =
    let val (s, p, m) = readWhites str
    in m <= p
    end

fun readWord str =
    let val (s, p, m) = readWhites str
        fun read p = if atEnd (s, p, m) orelse seperator (String.sub (s, p)) then p
                     else read (p + 1)
        val pos = read p
    in if pos = p then NONE
       else SOME (String.substring (s, p, pos - p), (s, pos, m))
    end

fun readVar str = omap (readWord str) (fn (s, rest) => (Var s, rest))

fun listToTerm []                      = NONE
  | listToTerm (x :: (Var "->") :: xs) = omap (listToTerm xs) (fn t => Arr (x, t))
  | listToTerm ((Var "->") :: xs)      = NONE
  | listToTerm [x]                     = SOME x
  | listToTerm [x, y]                  = SOME (App (x, y))
  | listToTerm (x :: y :: xs)          = listToTerm ((App (x, y)) :: xs)

fun splitAt c (s, p, m) =
    let fun findStop pos l =
	    if atEnd (s, pos, m) then NONE
	    else if String.sub (s, pos) = c andalso l = 0 then SOME pos
	    else if String.sub (s, pos) = #"(" then findStop (pos + 1) (l + 1)
	    else if String.sub (s, pos) = #")" then (if l = 0 then NONE
						     else findStop (pos + 1) (l - 1))
	    else findStop (pos + 1) l
    in omap (findStop p 0) (fn stop => ((s, p, stop), (s, stop + 1, m)))
    end

fun strMatch str (s, p, m) = m > p + (String.size str)
			     andalso String.substring (s, p, String.size str) = str

fun isLam str = strMatch "#l" str
fun isTLam str = strMatch "#L" str
fun isPi str = strMatch "#P" str

fun readTerm str =
    obnd (readList str)
         (fn l => listToTerm l)
and readList str =
    let val (s, p, m) = readWhites str
        fun readRest (t, rest) = omap (readList rest) (fn l => t :: l)
    in if atEnd (s, p, m) then SOME []
       else if isLam (s, p, m) then omap (readLam (s, p + 2, m)) (fn t => [t])
       else if isTLam (s, p, m) then omap (readParamBody (s, p + 2, m) TLam) (fn t => [t])
       else if isPi (s, p, m) then omap (readParamBody (s, p + 2, m) Pi) (fn t => [t])
       else if String.sub (s, p) = #"(" then obnd (readParen (s, p + 1, m)) readRest
       else obnd (readVar (s, p, m)) readRest
    end
and readLam str =
    let val pb = obnd (splitAt #"." str)
		      (fn ((s, p, m), b) =>
			  if strMatch "(" (s, p, m)
			  then obnd (splitAt #")" (s, p + 1, m))
				    (fn ((s, p, m2), _) => if m2 + 1 = m then SOME ((s, p, m2), b)
							   else NONE)
			  else SOME ((s, p, m), b))
	val pt = obnd pb
		      (fn (str, b) => obnd (readWord str)
					   (fn (p, rest) =>
					       (obnd (readChar #":" (readWhites rest))
						     (fn rest =>
							 omap (readTerm rest)
							      (fn ty => (p, ty, b))))))
    in obnd pt (fn (p, t, b) => omap (readTerm b) (fn bo => Lam (p, t, bo)))
    end
and readParamBody str ctr =
    let fun readT (p, str) = omap (readTerm str)
                                  (fn t => ctr (p, t))
        val param = obnd (readWord str)
                         (fn (p, str) => omap (readChar #"." str)
                                              (fn str => (p, str)))
    in obnd param readT
    end
and readParen str =
    obnd (splitAt #")" str)
         (fn (str, rest) => omap (readTerm str)
				 (fn t => (t, rest)))


fun isDef str =
    let val w = obnd (readWord str)
		     (fn (name, rest) => readWord rest)
    in case w of
	   SOME (":=", _) => true
	 | _              => false
    end

fun isSadface str =
    let val (s, p, m) = readWhites str
    in atEnd (s, p, m)
       orelse (m > p + 2
	       andalso String.substring (s, p, 2) = ":("
	       andalso atEnd (s, p + 2, m))
    end

fun readDef str = 
    let val name = obnd (readWord str)
			(fn (name, rest) => omap (readWord rest)
						 (fn (_, rest) => (name, rest)))
	val firstW = omap name (fn (_, rest) => isSadface rest)
    in case (name, firstW) of
	   (SOME (n, _), SOME true) => SOME (Undef n)
					       
	 | (SOME (n, rest), _)           => omap (readTerm rest)
						       (fn t => Def (Define (n, t)))
	 | _                             => NONE
    end

fun readStmt s =
    let val str = (s, 0, String.size s)
    in if isDef str then readDef str
       else omap (readTerm str) Term
    end

fun addDef def [] = [def]
  | addDef (Define (n1, t1))  (Define (n2, t2) :: xs) =
    if n1 = n2 then Define (n1, t1) :: xs
    else Define (n2, t2) :: addDef (Define (n1, t1)) xs

fun removeDef _ [] = []
  | removeDef s (Define (n, t) :: xs) =
    if s = n then xs
    else Define (n, t) :: removeDef s xs

fun renameTypes defs trm =
    let val types = List.filter (fn (Define (_, t)) => isType t [] t) defs
        fun renamePi p b [] = Pi (p, renameT b)
          | renamePi p b (Define (n, t) :: xs) = 
            if sameType trm [] [] (Pi (p, b)) t then Var n
            else renamePi p b xs
        and renameT (App (f, a)) = App (renameT f, renameT a)
          | renameT (Lam (p, t, b)) = Lam (p, renameT t, renameT b)
          | renameT (TLam (p, b)) = TLam (p, renameT b)
          | renameT (Arr (f, t)) = Arr (renameT f, renameT t)
          | renameT (Var s) = Var s
          | renameT (Pi (p, b)) = if isType trm [] trm then renamePi p b types
                                  else Pi (p, renameT b)
    in renameT trm
    end

fun typestr defs t = case typeof t [] t of
                         SOME t => " : " ^ termstr (renameTypes defs t)
                       | NONE   => if isType t [] t then " type"
                                   else " : typefail :("

fun handleStmt defs st =
    case st of
	Term t              => (reduceRename (renameDefs t defs), defs)
      | Def (Define (s, t)) => let val tt = (renameDefs t defs)
                               in (Other (s ^ typestr defs tt), addDef (Define (s, tt)) defs)
                               end
      | Undef s             => (Other (s ^ " :("), removeDef s defs)

fun nextExec res = case res of
		       Reduction (_, t)    => SOME t
		     | Rename (_, _, _, t) => SOME t
		     | Normal _            => NONE
		     | Other _             => NONE

fun execStr defs res = case res of
                           Reduction (_, t)      => termstr (renameTypes defs t) ^ typestr defs t
                         | Rename (s1, _, s2, t) => termstr (renameTypes defs t) ^
                                                    " | [" ^ s2 ^ "/" ^ s1 ^ "]" ^
                                                    typestr defs t
                         | Normal t              => termstr (renameTypes defs t) ^ typestr defs t
                         | Other s               => s

fun repl defs _ =
    let val inp = TextIO.inputLine TextIO.stdIn
	fun hTerm t = 
	    let val res = reduceRename t
		val resStr = "\n" ^ (execStr defs res)
	    in case nextExec res of
		   SOME t => (TextIO.print resStr; hTerm t)
		 | NONE   => defs
	    end
	fun hStmt defs st = 
	    let val (res, defs) = handleStmt defs st
		val resStr = execStr defs res
	    in case nextExec res of
		   SOME t => (TextIO.print resStr; hTerm t; defs)
		 | NONE   => (TextIO.print resStr; defs)
	    end
	fun handleString defs s =
	    case readStmt s of
		SOME st => hStmt defs st
	      | NONE    => (TextIO.print ":("; defs)
    in case inp of
           NONE          => OS.Process.failure
         | SOME "end.\n"   => OS.Process.success
         | SOME s        => repl (handleString defs s) ()
    end


