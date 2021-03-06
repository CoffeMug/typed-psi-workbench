(* uses missing
        /psiTyped
        /simulator
        /weak 
*)


signature SYMBOLIC_BISIM_CONSTRAINT =
sig
  structure Psi : PSI

  datatype constraint
    (* transition constraints *)
    = True
    | False
	(* the transition constraint is typed *)
    | Atomic of (Psi.Inst.name * Psi.Inst.ty) list * Psi.Inst.assertion * Psi.Inst.condition
    (* constraints *)
    | TermEq of Psi.Inst.term  * Psi.Inst.term
    | FreshP of Psi.Inst.name  * Psi.psi
    (* TODO: a bug, this must be frames *)
    | StImp  of Psi.Inst.assertion * Psi.Inst.assertion

    | Conj   of constraint * constraint
    | Disj   of constraint * constraint
    | Imp    of constraint * constraint

  include NOMINAL
    where type atom = Psi.Inst.name
    where type data = constraint
	sharing AtomSort = Psi.Inst.Sort

  val subst : constraint -> (Psi.Inst.name * Psi.Inst.term) list -> constraint

  val simplify : constraint -> constraint
  val cnf      : constraint -> constraint
  val dnf      : constraint -> constraint
  val rewrite  : (constraint -> constraint option) list
               -> constraint -> constraint


  val simplificationRules : (constraint -> constraint option) list
  val deMorganAndNegRules : (constraint -> constraint option) list
  val elimImpRules        : (constraint -> constraint option) list
  val disjRules           : (constraint -> constraint option) list

  val disjunct : constraint list -> constraint
  val conjunct : constraint list -> constraint
end;



signature SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
sig
  structure Psi        : PSI
  structure Constraint : SYMBOLIC_BISIM_CONSTRAINT

  val solve :
    (string -> Constraint.constraint -> unit) -> Constraint.constraint ->( Psi.Inst.condition list list ,((Psi.Inst.name * Psi.Inst.term) list * Psi.Inst.assertion) list) Either.either


  sharing Constraint.Psi = Psi
end;


functor SymBisimConstraint(Psi: PSI) : SYMBOLIC_BISIM_CONSTRAINT =
struct
  datatype constraint
    (* transition constraints *)
    = True
    | False
    | Atomic of (Psi.Inst.name * Psi.Inst.ty) list * Psi.Inst.assertion * Psi.Inst.condition
    | Conj   of constraint * constraint
    (* constraints *)
    | TermEq of Psi.Inst.term * Psi.Inst.term
    | FreshP of Psi.Inst.name * Psi.psi
    | Disj   of constraint    * constraint
    | Imp    of constraint    * constraint
    | StImp  of Psi.Inst.assertion * Psi.Inst.assertion

  structure Psi = Psi

  open Psi
  open Inst

  structure Nom = Nominal(
  struct
    type atom = name
    type data = constraint
    structure L = NominalNameList(Term)

  	structure AtomSort = Term.AtomSort
    structure DataSort = struct datatype sort = SBConstraint fun eq _ = true end
    val atomSort = Term.atomSort
    fun dataSort _ = DataSort.SBConstraint

	(* swap function defined for typed lists *)
	fun swap_tvec ab [] = []
	| swap_tvec ab ((a,t)::rest) = 
	(Inst.Term.swapAtom ab a, Inst.Type.swap ab t)::(swap_tvec ab rest)



    fun swap (a,b) True = True
      | swap (a,b) False = False
      | swap (a,b) (Atomic (avec, psi, phi)) =
        Atomic (swap_tvec (a,b) avec, Assr.swap (a,b) psi, Cond.swap (a,b) phi)
      | swap (a,b) (Conj (c,c'))    = Conj (swap (a,b) c, swap (a,b) c')
      | swap (a,b) (TermEq (n,m))   = TermEq (Term.swap (a,b) n, Term.swap (a,b) m)
      (* TODO: Should swapping effect freshness constraints? *)
      | swap (a,b) (FreshP (x,p))   = FreshP (x, Psi.swap (a,b) p)
      | swap (a,b) (Disj (c,c'))    = Disj (swap (a,b) c, swap (a,b) c')
      | swap (a,b) (Imp (c,c'))     = Imp (swap (a,b) c, swap (a,b) c')
      | swap (a,b) (StImp (f,g))    = StImp (Assr.swap (a,b) f, Assr.swap (a,b) g)

    fun support True = []
      | support False = []
      | support (Atomic (avec, psi, phi)) =
        Lst.minus ((Assr.support psi) @ (Cond.support phi)) (Lst.fsl avec)
      | support (Conj (c,c'))    = support c @ support c'
      | support (TermEq (n,m))   = Term.support n @ Term.support m
      (* TODO: what is support of this? *)
      | support (FreshP (a,p))   = Psi.support p
      | support (Disj (c,c'))    = support c @ support c'
      | support (Imp (c,c'))     = support c @ support c'
      | support (StImp (f,g))    = Assr.support f @ Assr.support g

    val new = Term.new

    fun eq aEq (True,True) = true
      | eq aEq (False,False) = true
      | eq aEq (Atomic ([],psi,phi), Atomic ([],psi',phi')) =
            Assr.eqData (psi, psi') andalso Cond.eqData(phi,phi')
      | eq aEq (Atomic ((a,t)::avec,psi,phi), Atomic ((a',t')::avec',psi',phi')) =
            Type.eqData (t,t') andalso 
			aEq ((a, Atomic (avec,psi,phi)), (a', Atomic (avec', psi', phi')))
      | eq aEq (Atomic _, Atomic _) = false
      | eq aEq (Conj (c1,c1'), Conj (c2,c2')) = eq aEq (c1, c2) andalso eq aEq (c1',c2')
      | eq aEq (Disj (c1,c1'), Disj (c2,c2')) = eq aEq (c1, c2) andalso eq aEq (c1',c2')
      | eq aEq (Imp  (c1,c1'), Imp  (c2,c2')) = eq aEq (c1, c2) andalso eq aEq (c1',c2')
      | eq aEq (TermEq (n,m), TermEq(n',m')) = Term.eqData (n,n') andalso Term.eqData (m,m')
      | eq aEq (FreshP (a,p), FreshP (a',p')) = a = a' andalso Psi.eqData (p,p')
      | eq aEq (StImp (f,g), StImp (f',g')) = Assr.eqData (f,f') andalso Assr.eqData (g,g')
      | eq _ _ = false
  end)
  open Nom

  structure NA = NominalAlpha(Nom)
  local open Missing in

  fun subst True sigma             = True
    | subst False sigma            = False
    | subst (Conj (c,c')) sigma    = Conj (subst c sigma, subst c' sigma)
    | subst (Disj (c,c')) sigma    = Disj (subst c sigma, subst c' sigma)
    | subst (Imp  (c,c')) sigma    = Imp  (subst c sigma, subst c' sigma)
    | subst (TermEq (n,m)) sigma   = TermEq (substT sigma n, substT sigma m)
    | subst (FreshP (a,p)) sigma   = FreshP (a, Psi.subst p sigma)
    | subst (StImp (f,g)) sigma    = StImp (substA sigma f, substA sigma g)
    | subst (Atomic (avec, psi, phi)) sigma =
        (* avec # sigma *)
        let
          val sigmaNames = (map Tpl.fst sigma) @
                           (List.concat (map (Term.support o Tpl.snd) sigma))
        in
          (NA.makeFresh (Lst.fsl avec) (Atomic (avec, psi, phi)) sigmaNames) |>
          (fn (Atomic (avec, psi, phi)) =>
            Atomic (avec, substA sigma psi, substC sigma phi)
            | _ => Err.undefined ())
        end
  end



  fun applyRule [] t = NONE
    | applyRule (r::rs) t =
    case r t of
         NONE => applyRule rs t
       | t' => t'

  fun rbin rules rw'' constr (c,c') =
  let
    val (c,rw)   = rewrite' rules c
    val (c',rw') = rewrite' rules c'
  in
    (constr (c,c'), rw orelse rw' orelse rw'')
  end

  and rewrite' rules c =
  let
    val (c,rw) = case applyRule rules c of
                       NONE    => (c , false)
                     | SOME c' => (c', true )
  in
    case c of
         Imp c  => rbin rules rw Imp  c
       | Conj c => rbin rules rw Conj c
       | Disj c => rbin rules rw Disj c
       | c      => (c,rw)
  end

  fun rewrite rules c =
  let
    val (c, rw) = rewrite' rules c
  in
    if rw then rewrite rules c else c
  end

  fun listOfDisjuncts (Disj (c,c')) = listOfDisjuncts c @ listOfDisjuncts c'
    | listOfDisjuncts c = [c]

  fun listOfConjuncts (Conj (c,c')) = listOfConjuncts c @ listOfConjuncts c'
    | listOfConjuncts c = [c]

  val maybe = Missing.maybe
  val const = Missing.const


  fun findNeg (Imp (c, False)) cs =
    maybe false (const true) (List.find (fn c' => eqData(c, c')) cs)
    | findNeg c cs =
    maybe false (const true)
    (List.find (fn c' => eqData(Imp(c,False), c')) cs)

  fun hasCandNC []      = false
    | hasCandNC [c]     = false
    | hasCandNC (c::cs) = findNeg c cs orelse hasCandNC cs

  val simplificationRules =
    (fn (Conj (False,_)) => SOME False      | _ => NONE) ::
    (fn (Conj (_,False)) => SOME False      | _ => NONE) ::
    (fn (Conj (True,c))  => SOME c          | _ => NONE) ::
    (fn (Conj (c,True))  => SOME c          | _ => NONE) ::
    (fn (Conj (c,c')) =>
        if eqData (c,c') then SOME c else NONE | _ => NONE) ::

    (* c /\ (c' \/ c'') = c *)
    (fn (Conj (c, Disj (c',c''))) =>
        if eqData (c, c') orelse eqData (c, c'') then SOME c
        else NONE                           | _ => NONE) ::
    (fn (Conj (Disj (c',c''), c)) =>
        if eqData (c, c') orelse eqData (c, c'') then SOME c
        else NONE                           | _ => NONE) ::

    (fn (Disj (True,_))  => SOME True       | _ => NONE) ::
    (fn (Disj (_,True))  => SOME True       | _ => NONE) ::
    (fn (Disj (False,c)) => SOME c          | _ => NONE) ::
    (fn (Disj (c,False)) => SOME c          | _ => NONE) ::
    (fn (Disj (c,c')) =>
        if eqData (c,c') then SOME c else NONE | _ => NONE) ::

    (* c \/ (c' /\ c'') = c *)
    (fn (Disj (c, Conj (c',c''))) =>
        if eqData (c, c') orelse eqData (c, c'') then SOME c
        else NONE                           | _ => NONE) ::
    (fn (Disj (Conj (c',c''), c)) =>
        if eqData (c, c') orelse eqData (c, c'') then SOME c
        else NONE                           | _ => NONE) ::

    (fn (Imp (False, _)) => SOME True       | _ => NONE) ::
    (fn (Imp (c, True))  => SOME True       | _ => NONE) ::
    (fn (Imp (True, c))  => SOME c          | _ => NONE) ::

    (*
    (fn (Disj (c, c')) =>
        if eqD (c,c') then SOME c else NONE
                                            | _ => NONE) ::
    (fn (Conj (c, c')) =>
        if eqD (c,c') then SOME c else NONE
                                            | _ => NONE) ::
                                            *)

    (* LEM *)
    (fn (c as (Disj (c',c''))) =>
      if hasCandNC (listOfDisjuncts c)  then SOME True else NONE
                                            | _ => NONE) ::

    (* Contradiction *)
    (fn (c as (Conj (c', c''))) =>
        if hasCandNC (listOfConjuncts c) then SOME False else NONE
                                            | _ => NONE) ::

    (* neg neg C = C *)
    (fn (Imp (Imp (c, False), False)) => SOME c
                                            | _ => NONE) ::

    []

  fun simplify c = rewrite simplificationRules c

  fun neg c = Imp (c, False)

  val elimImpRules =
                                            (*
    (fn (Imp (c,False)) => NONE
      | (Imp (c,c'))    => SOME (Disj (c', Imp (c,False)))
                                            | _ => NONE) ::
                                            *)
    (fn (Imp (c,False)) => NONE (* Skip the negation *)
      | (Imp (c,c'))    => SOME (Disj (Imp (c,False), c'))
                                            | _ => NONE) ::
    []


  val deMorganAndNegRules =
    (fn (Imp (Conj (c,c'), False)) =>
        SOME (Disj (neg c, neg c'))
                                            | _ => NONE) ::
    (fn (Imp (Disj (c,c'), False)) =>
        SOME (Conj (neg c, neg c'))
                                            | _ => NONE) ::

    (fn (Imp (Imp (c, False), False)) => SOME c
                                            | _ => NONE) ::

    []

  val disjRules =
    (fn (Disj (c, Conj (c', c''))) =>
        SOME (Conj (Disj (c, c'), Disj (c,c'')))
                                            | _ => NONE) ::
    (fn (Disj (Conj (c,c'), c'')) =>
        SOME (Conj (Disj (c, c''), Disj (c',c'')))
                                            | _ => NONE) ::
    []

  val conjRules =
    (fn (Conj (c, Disj (c', c''))) =>
        SOME (Disj (Conj (c, c'), Conj (c,c'')))
                                            | _ => NONE) ::
    (fn (Conj (Disj (c,c'), c'')) =>
        SOME (Disj (Conj (c, c''), Conj (c',c'')))
                                            | _ => NONE) ::
    []


  fun cnf c =
  let
    val c = simplify c
    val c = rewrite elimImpRules c
    val c = rewrite deMorganAndNegRules c
    val c = rewrite disjRules c
    val c = simplify c
  in
    c
  end

  fun dnf c =
  let
    val c = simplify c
    val c = rewrite elimImpRules c
    val c = rewrite deMorganAndNegRules c
    val c = rewrite conjRules c
    val c = simplify c
  in
    c
  end

  fun reduce f base []      = base
    | reduce f base [x]     = x
    | reduce f base (x::xs) = f (x, reduce f base xs)

  fun disjunct cs = reduce Disj False cs
  fun conjunct cs = reduce Conj True cs

end;

signature BISIM =
sig
  structure Psi: PSI
  structure C  : SYMBOLIC_BISIM_CONSTRAINT

  val bisim :
    Psi.psi * Psi.psi ->
        C.constraint * (((Psi.psi * Psi.psi) * C.constraint) list)

  sharing Psi = C.Psi
end;


functor Bisim(A: sig
  structure WSim: WEAK_SYMBOLIC_PSI_SIMULATOR
  structure C : SYMBOLIC_BISIM_CONSTRAINT
  structure SymPsi : SYMBOLIC_PSI

  sharing C.Psi = WSim.Sim.Psi= SymPsi.Psi
end) : BISIM =
struct
  open Missing
  open A

  structure Psi = WSim.Sim.Psi
  (* structure C   = SymBisimConstraint(Psi) *)
  structure F   = Frame(Psi)
  structure R   = StrongSymbolicTransitionResidual(WSim.Sim.Tr)
  structure RA  = NominalAlpha(R)
  structure L   = NominalNameList(Psi.Inst.Term)

  open C

  fun permute swap pi t =
    List.foldr (fn ((a,b), t) => swap (a,b) t) t pi

  fun unvar x = hd $ Psi.Inst.Term.support x

  fun framePsi p = F.f p |> F.assertion

  val emptyT        = []
  fun joinT (w,w')  = w @ w'
  fun unionT ts     = List.foldr joinT emptyT ts
  fun snglT (p,q) c = [((p,q), c)]

  fun inW ((p,q), w) =
    maybe false (const true) $
        List.find (fn (p',q') => Psi.eqData (p,p') andalso Psi.eqData (q,q')) w


  val emptyEnv = WSim.Sim.ClEnv.empty
  val unitPsi = Psi.Inst.unit

  fun translateC []         = True
    | translateC [c]        = Atomic c
    | translateC (c::cstrs) = Conj (Atomic c, translateC cstrs)

  fun collectCstrDeriv trs =
    map (fn (psi,p,alpha,c,p') => (translateC c,p')) trs


  fun freshness avec p =
    List.foldr (fn (a,c) => FreshP (a,p) </Conj/> c) True avec

  fun silent p = WSim.silent emptyEnv unitPsi p

  fun strictTau p =
    List.filter (fn (psi,p,WSim.Sim.Tr.Act.Tau,c,p') => true
                  | _ => false
                ) $ WSim.Sim.reduce emptyEnv unitPsi p

  fun strictOut p =
    List.filter (fn (psi,p,WSim.Sim.Tr.Act.Output _,c,p') => true
                  | _ => false
                ) $ WSim.Sim.reduce emptyEnv unitPsi p

  fun strictIn p =
    List.filter (fn (psi,p,WSim.Sim.Tr.Act.Input _,c,p') => true
                  | _ => false
                ) $ WSim.Sim.reduce emptyEnv unitPsi p

  fun weakOut p =
    List.filter (fn (psi,p,WSim.Tr.Output _,c,p') => true | _ => false
                ) $ WSim.reduce emptyEnv unitPsi p

  fun weakIn p =
    List.filter (fn (psi,p,WSim.Tr.Input _,c,p') => true | _ => false
                ) $ WSim.reduce emptyEnv unitPsi p

  val xNames       = ref ([] : Psi.Inst.name list)
  fun addName a    = xNames := (a :: !xNames)
  fun usedNames () = !xNames
  fun resetNames ()= xNames := []
  fun newName xvec =
  let
    val y = Psi.Inst.Term.new (SymPsi.nameOfConstrSort ()) xvec
    val () = addName y
  in
    y
  end

  fun matchStImp (p,q) c w =
  let
    val qtr = collectCstrDeriv $ silent q
    val (cvec,tvec) = ListPair.unzip $ map
        (fn (cqi, qi) =>
            let val (ci, ti) = close (p,qi) (c </Conj/> cqi) ((p,q)::w)
            in (cqi </Conj/> ci </Conj/>
                ((ci </Conj/> cqi) </Imp/> StImp (framePsi p, framePsi qi)),
                ti)
            end) qtr
  in
    (True </Imp/> disjunct cvec, unionT tvec)
  end


  and matchTau (p,q) c w =
  let
    val ptr = collectCstrDeriv $ strictTau p
    val qtr = collectCstrDeriv $ silent q
    val (cvec,tvec) = ListPair.unzip $ map (fn (cpi,pi) =>
        let val (civec, tivec) = ListPair.unzip $ map (fn (cqj,qj) =>
            let val (cij,tij) =
                close (pi,qj) (c </Conj/> cpi </Conj/> cqj) ((p,q) :: w)
            in
			   (cqj </Conj/> cij, tij)
			 end) qtr
		 in
		   (cpi </Imp/> disjunct civec, unionT tivec)
		 end) ptr
   in
	 (conjunct cvec, unionT tvec)
   end

   (* i have made some changes (Lst.fsl) in this to make it work *)
   and matchOut (p,q) c w =
   let
	 val ptr = (strictOut p) |> map
		 (fn (psi,p,(WSim.Sim.Tr.Act.Output (y', avec, n)), cpi, pi) =>
			 let
			   val supP = Psi.support p
			   val supQ = Psi.support q
			   val supC = C.support c
			   val y    = newName (supP @ supQ @ supC @ usedNames ())
			   val cpi  = C.swap (y, unvar y')
								 (translateC cpi)
			 in
			   (RA.makeFresh (Lst.fsl avec) (WSim.Sim.Tr.Act.Output (y',avec,n), pi)
				 ([y] @ supP @ supQ @ supC @ (C.support cpi))) |>
				 (fn (WSim.Sim.Tr.Act.Output (_, avec, n), pi) =>
					 ((y, (Lst.fsl avec), n), cpi, pi)
				   | _ => Err.undefined ())
			 end
		   | _ => Err.undefined ())

	 val (cvec, tvec) = ListPair.unzip $ map (fn ((y,avec,n), cpi, pi) =>
		 let
		   val qtr = weakOut q
			 |> List.filter (fn (_,_,WSim.Tr.Output (z,cvec,n'),_,_) =>
				 length cvec = length avec | _ => false)
			 |> map
			 (fn (psi,q,WSim.Tr.Output (z,cvec,n'),cqj,qj) =>
				 ((y, avec, permute Psi.Inst.Term.swap (zip avec (Lst.fsl cvec)) n'),
				  C.swap (unvar z, y) (translateC cqj),
				  permute Psi.swap (zip avec (Lst.fsl cvec)) qj)
			   | _ => Err.undefined () )
		   val (civec,tivec) = ListPair.unzip $ map (fn ((z,cvec,n'),cqj,qj) =>
			 let
			   val (cij,tij) =
				 close (pi,qj)
					   (c </Conj/> cpi </Conj/>
					   (n </TermEq/> n') </Conj/>
					   freshness avec p </Conj/> freshness avec q)
					   ((p,q)::w)
			 in
			   (cpi </Conj/> (n </TermEq/> n') </Conj/> cij, tij)
			 end ) qtr
		 in
		   ((cpi </Conj/> freshness avec p </Conj/> freshness avec q)
			 </Imp/> disjunct civec,
			 unionT tivec)
		 end) ptr
   in
	 (conjunct cvec, unionT tvec)
   end

   and matchIn (p,q) c w =
   let
	 val ptr = strictIn p |> map
		 (fn (psi,p,WSim.Sim.Tr.Act.Input (y',x'),cpi,pi) =>
		  let
			val supP = Psi.support p
			val supQ = Psi.support q
			val supC = C.support c
			val y    = newName (supP @ supQ @ supC @ usedNames ())
			val cpi  = C.swap (y, unvar y')
							  (translateC cpi)
			val supCpi = C.support cpi
			val x = Psi.Inst.Term.new x' (y :: supP @ supQ @ supC @ supCpi)
			val pi = Psi.swap (x,x') pi
		  in
			((y, x), cpi, pi)
		  end | _ => Err.undefined () )
	 val (cvec,tvec) = ListPair.unzip (map (fn ((y,x), cpi, pi) =>
		 let
		   val qtr = weakIn q |> map (fn (psi,q,WSim.Tr.Input (z,x'),cqj,qj) =>
			 ((y, x), C.swap (y,unvar z) (translateC cqj), Psi.swap (x,x') qj)
			 | _ => Err.undefined () )
		   val (civec,tivec) = ListPair.unzip (map (fn ((z,x),cqj,qj) =>
			 let
			   val (cij,tij) =
				 close (pi,qj)
					   (c </Conj/> cpi </Conj/> cqj)
					   ((p,q)::w)
			 in (cqj </Conj/> cij, tij) end) qtr)
		 in
		   (cpi </Imp/> disjunct civec, unionT tivec)
		 end) ptr)
   in
	 (conjunct cvec, unionT tvec)
   end

   and close (p,q) c w =
	 if (p,q) </inW/> w then
	   (True, emptyT)
	 else
	   let
		 val (c_stimp,  t_stimp ) = matchStImp (p,q) c w
		 val (c'_stimp, t'_stimp) = matchStImp (q,p) c w
		 val (c_tau, t_tau)       = matchTau (p,q) c w
		 val (c'_tau, t'_tau)     = matchTau (q,p) c w
		 val (c_out, t_out)       = matchOut (p,q) c w
		 val (c'_out, t'_out)     = matchOut (q,p) c w
		 val (c_in, t_in)         = matchIn (p,q) c w
		 val (c'_in, t'_in)       = matchIn (q,p) c w
      in
        (c_stimp </Conj/> c'_stimp </Conj/>
         c_tau </Conj/> c'_tau </Conj/>
         c_out </Conj/> c'_out </Conj/>
         c_in </Conj/> c'_in
        ,
        (t_stimp </joinT/> t'_stimp </joinT/>
        t_tau </joinT/> t'_tau </joinT/>
        t_out </joinT/> t'_out </joinT/>
        t_in </joinT/> t'_in </joinT/>
        (snglT (p,q) (c </Conj/> c_stimp </Conj/> c_tau </Conj/>
                      c_out </Conj/> c_in)) </joinT/>
        (snglT (q,p) (c </Conj/> c'_stimp </Conj/> c'_tau </Conj/>
                      c'_out </Conj/> c'_in)) ) )
      end

  and bisim (p,q) =
  let
    val () = resetNames ()
  in
    close (p,q) True emptyT
  end

end;
