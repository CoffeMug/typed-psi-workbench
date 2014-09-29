(* uses src/missing,
        src/nominal,
        src/env,
        src/sort
*)


signature PSI_INSTANCE =
sig
  eqtype name

  structure Term: NOMINAL
  structure Cond: NOMINAL
  structure Assr: NOMINAL
  structure Type: NOMINAL

  sharing type name = Term.atom = Cond.atom = Assr.atom = Type.atom

  structure Sort : SORT


  sharing Term.AtomSort = Cond.AtomSort = Assr.AtomSort = Type.AtomSort = Sort
  sharing Term.DataSort = Sort

  val canRecv : Sort.sort -> Sort.sort -> bool
  val canSend : Sort.sort -> Sort.sort -> bool
  val canSubs : Sort.sort -> Sort.sort -> bool

  val isNameSort : Sort.sort -> bool

  type term      = Term.data
  type condition = Cond.data
  type assertion = Assr.data
  type ty        = Type.data 

  structure Env : TYPE_ENVIRONMENT
                  where type name  = name 
                  where type typ   = ty
                  where type asser = assertion 

  exception TypeErr of string
 
  val chaneq  : term * term -> condition
  val compose : assertion * assertion -> assertion
  val unit    : assertion
  val entails : assertion * condition -> bool

  val substT  : (name * term) list -> term      -> term
  val substC  : (name * term) list -> condition -> condition
  val substA  : (name * term) list -> assertion -> assertion
  val substTy : (name * term) list -> ty -> ty        

  
  (** functions required by the type-checker ********)
  val compatIn     : Env.env -> ty -> ty -> bool
  val compatOut    : Env.env -> ty -> ty -> bool

  val checkT       : Env.env -> term -> ty 
  val checkA       : Env.env -> assertion -> unit
  val checkC       : Env.env -> condition -> unit
  val checkAbs     : Env.env -> (name * ty) list -> term -> ty
  
end;


signature PSI =
sig
  structure Inst: PSI_INSTANCE

  datatype psi
    = Nil
    (* Output (m, n, p) == 'M<N>.P  *)
    | Output      of Inst.term * Inst.term * psi
    (* Input (m, xvec, n, p) == M(\xvec)N.P *)
    | Input       of Inst.term * (Inst.name * Inst.ty) list * Inst.term * psi
    | Case        of (Inst.condition * psi) list
    | Restriction of Inst.name * Inst.ty * psi
    | Parallel    of psi * psi
    | Replication of psi
    | Assertion   of Inst.assertion
    (* Invocation (a, mvec) == A<Mvec> *)
    | Invocation  of Inst.term * (Inst.term list)

  include NOMINAL
    where type atom = Inst.name
    where type data = psi
    sharing AtomSort = Inst.Sort
    (* sharing DataSort = Inst.Sort *)

  (* Substitution function *)
  val subst : psi -> (Inst.name * Inst.term) list -> psi
end;

signature FRAME =
sig
  structure Psi: PSI

  type frame

  (* compute the frame of a psi agent *)
  val f          : Psi.psi -> frame
  val unit_frame : frame
  val compose    : frame -> frame -> frame

  val assertion  : frame -> Psi.Inst.assertion
  val binders    : frame -> (Psi.Inst.name * Psi.Inst.ty) list

  include NOMINAL
  sharing AtomSort = Psi.AtomSort
  sharing type atom = Psi.Inst.name
  sharing type data = frame
end;


functor Frame(P: PSI): FRAME =
struct
  structure Psi = P
  local open P in

  datatype frame = Frame of (Inst.name * Inst.ty) list * Inst.assertion

  val unit_frame                       = Frame ([], Inst.unit)
  fun extend_names ns (Frame (fns, a)) = Frame (ns @ fns, a)

  fun assertion (Frame ( _, a)) = a
  fun binders   (Frame ( nt,_))  = nt
  fun frame n a = Frame (n,a)

  structure L = NominalNameList(Inst.Term)

  structure Nom = Nominal(
  struct
    structure AtomSort = Psi.Inst.Sort
    structure DataSort = struct datatype sort = FrameSort fun eq _ = true end
    type atom = Inst.name
    type data = frame

    val atomSort = Psi.Inst.Term.atomSort
    fun dataSort _ = DataSort.FrameSort


    (* auxilary functions used by support & swap function. *)

    fun extract_n (Frame([],a)) = []
      | extract_n (Frame(((n,t)::rest),a)) = 
        n::extract_n (Frame(rest,a))

    fun extract_t (Frame([],a)) = []
      | extract_t (Frame(((n,t)::rest),a)) = 
        t::extract_t (Frame(rest,a))

    fun apply_swap_nt pi [] = []
      | apply_swap_nt pi ((n,t)::rest) = 
        (Inst.Term.swapAtom pi n, Inst.Type.swap pi t):: apply_swap_nt pi rest


    (*******************************************************)


    fun swap pi (Frame (avec, a)) =
      let val swap_list = binders (Frame(avec,a))
      in 
        Frame ( apply_swap_nt pi swap_list , Inst.Assr.swap pi a)
      end


    fun support (Frame (avec , psi)) =
      Lst.minus (Inst.Assr.support psi) (extract_n (Frame (avec , psi))) 

    val new = P.new

    fun eq alphaEq (Frame ([], psi1), Frame ([], psi2)) =
            Inst.Assr.eqData (psi1, psi2)
      | eq alphaEq (Frame ([], psi1), Frame (bvec, psi2)) = false
      | eq alphaEq (Frame (avec, psi1), Frame ([], psi2)) = false
      | eq alphaEq (Frame ((a,t)::avec, psi1), Frame ((b,t')::bvec, psi2)) =
            List.length avec = List.length bvec andalso
            alphaEq ((a, Frame (avec, psi1)),(b, Frame (bvec, psi2))) andalso
        Inst.Type.eqData (t,t') 
       
  end)


  open Nom

  structure FrameAlpha = NominalAlphaTyped(Nom)

  fun compose (fA as Frame (avecA, psiA)) (fB as Frame (avecB, psiB)) =
  let (* avecA # avecB *)

    fun extract_n (Frame([],a)) = []
      | extract_n (Frame(((n,t)::rest),a)) = 
        n::extract_n (Frame(rest,a))


    val Frame (avecA, psiA) = FrameAlpha.makeFresh (extract_n fA) fA fB
    val Frame (avecB, psiB) = FrameAlpha.makeFresh (extract_n fB) fB fA
 
  in
    Frame (avecA @ avecB, P.Inst.compose (psiA, psiB))
  end

  fun f (Input _)             = unit_frame
    | f (Output _)            = unit_frame
    | f (Case _)              = unit_frame
    | f (Replication _)       = unit_frame
    | f (Assertion a)         = Frame ([], a)
    | f (Parallel (p, q))     = compose (f p) (f q)
    | f (Restriction (n,t,p)) = extend_names [(n,t)] (f p) 
    | f (Nil)                 = unit_frame
    | f (Invocation _)        = unit_frame

end;
end;


signature PSI_CLAUSE =
sig
  structure Psi: PSI

  type clause =
    Psi.Inst.term * (Psi.Inst.name * Psi.Inst.ty) list * Psi.psi

  include NOMINAL
    where type atom = Psi.Inst.name
    where type data = clause

end;


functor PsiClause(P: PSI): PSI_CLAUSE =
struct
  structure Psi = P

  structure AtomSort = Psi.Inst.Sort
  structure DataSort = struct datatype sort = ClauseSort fun eq _ = true end

  type clause =
    P.Inst.term * (Psi.Inst.name * Psi.Inst.ty) list * P.psi

  type atom = P.Inst.name
  type data = clause

  val atomSort = Psi.Inst.Term.atomSort
  fun dataSort _ = DataSort.ClauseSort

  val swapAtom = P.Inst.Term.swapAtom
  val new = P.Inst.Term.new

  fun eqData _ = Err.error "TODO: define alpha equivalence for clauses"
  (* auxiliary function to handle swap on name-type pairs *)
  fun apply_swap_nt pi [] = []
    | apply_swap_nt pi ((n,t)::rest) = 
      (Psi.Inst.Term.swapAtom pi n, Psi.Inst.Type.swap pi t):: apply_swap_nt pi rest

  structure L = NominalNameList(Psi.Inst.Term)

  (* swaping does not effect the 'a' *)
  fun swap pi (a, xvec, p) =
    (a, apply_swap_nt pi xvec, P.swap pi p)

  fun support (a, xvec, p) =
    Lst.minus (P.support p) (Lst.fsl xvec)

  fun fresh n cl = not(Lst.member n (support cl))
end;


signature PSI_CLAUSE_ENVIRONMENT =
sig
  structure Cl : PSI_CLAUSE
  include ENVIRONMENT
    where type key = Cl.Psi.Inst.term
    where type value = Cl.clause
end;

functor PsiClauseEnvironment(C : PSI_CLAUSE) : PSI_CLAUSE_ENVIRONMENT =
struct
  open Missing;
  structure Cl = C

  type key   = C.Psi.Inst.term
  type value = C.clause
  type env   = (key * value) list

  fun eq a b = Cl.Psi.Inst.Term.eqData (a,b)

  fun extend e k v = (k,v)::e

  fun find e k =
    map snd $ Lst.filter ((eq k) o fst) e

  fun dom e = map fst e

  fun remove e k = Lst.filter (not o eq k o fst) e

  val empty = []
end;

functor Psi(I: PSI_INSTANCE): PSI =
struct
  open Fun

  type name      = I.name
  type term      = I.term
  type assertion = I.assertion
  type condition = I.condition
  type ty        = I.ty


  datatype psi
    = Nil
    (* Output (m, n, p) == 'M<N>.P  *)
    | Output      of term * term * psi
    (* Input (m, xvec, n, p) == M(\xvec)N.P *)
    | Input       of term * (name * ty) list * term * psi
    | Case        of (condition * psi) list
    | Restriction of name * ty * psi
    | Parallel    of psi * psi
    | Replication of psi
    | Assertion   of assertion
    | Invocation  of term * (term list)

  (* aliases *)
  val swapT      = I.Term.swap
  val swapC      = I.Cond.swap
  val swapA      = I.Assr.swap
  val swapTy     = I.Type.swap
  val supportT   = I.Term.support
  val supportC   = I.Cond.support
  val supportA   = I.Assr.support
  val supportTy  = I.Type.support
  val substT     = I.substT
  val substC     = I.substC
  val substA     = I.substA
  val substTy    = I.substTy

  structure Inst = I


  structure Nom = Nominal(
  struct
    type atom = name
    type data = psi

    structure AtomSort = Inst.Sort
    structure DataSort = struct datatype sort = PsiSort fun eq _ = true end

    val atomSort = Inst.Term.atomSort
    fun dataSort _ = DataSort.PsiSort

    val new        = I.Term.new

 
    structure L = NominalNameList(I.Term)


    (* auxilary function used to implement swap for typed vectors *)
     
    fun swap_tvec ab [] = []
      | swap_tvec ab ((a,t)::rest) = 
        (I.Term.swapAtom ab a, I.Type.swap ab t)::(swap_tvec ab rest)

    fun extract_n [] = []
      | extract_n ((n,t)::rest)  = 
        n::extract_n rest


    fun extract_t [] = []
      | extract_t ((n,t)::rest)  = 
        t::extract_t rest

    (**************************************************************************)
    fun swap _  Nil = Nil
      | swap ab (Output (m, n, p)) =
          Output (swapT ab m, swapT ab n, swap ab p)
      | swap ab (Input (m, xvec, n, p)) =
          Input (swapT ab m, swap_tvec ab xvec, swapT ab n,
                 swap ab p)
      | swap ab (Case cases) =
          Case (map (fn (c, p) => (swapC ab c, swap ab p)) cases) 

      | swap ab (Restriction (n,t,p)) =
          Restriction (I.Term.swapAtom ab n, I.Type.swap ab t, swap ab p) (* type support *)
      | swap ab (Parallel (p, q)) =
          Parallel (swap ab p, swap ab q)
      | swap ab (Replication p) =
          Replication (swap ab p)
      | swap ab (Assertion psi) =
          Assertion (swapA ab psi)
      | swap ab (Invocation (a,mvec)) =
          Invocation (a, map (swapT ab) mvec)

    fun filter_binders names name_list =
      List.filter (fn n => not(Lst.member n names)) name_list


    fun support Nil = []
      | support (Output (m,n,p)) = supportT m @ supportT n @ support p
      | support (Input (m,xvec,n,p)) =
        supportT m @ (Lst.minus (supportT n @ support p) (Lst.fsl xvec)) 
        @ (List.concat (map supportTy (Lst.scl xvec)))
      | support (Case cases) =
        List.concat (map (fn (phi,p) =>
                            supportC phi @ support p) cases)

      | support (Restriction (a,t,p)) = Lst.minus (support p @ supportTy t) [a] 
      | support (Parallel (p,q)) = support p @ support q
      | support (Replication p) = support p
      | support (Assertion psi) = supportA psi
      | support (Invocation (a, mvec)) = List.concat (map supportT mvec)

    structure TVec = NominalList(I.Term)



    fun eq alphaEq (Nil,Nil) = true
      | eq alphaEq (Output (m,n,p), Output (m',n',p')) =
        I.Term.eqData (m,m') andalso I.Term.eqData (n,n') andalso
        eq alphaEq (p,p')

      | eq alphaEq (Input (m,xvec,n,p), Input (m',xvec',n',p')) =
                List.length xvec = List.length xvec'
        andalso I.Term.eqData(m, m')
        andalso
            (case (Lst.fsl xvec) of
                 [] => I.Term.eqData (n,n') andalso eq alphaEq (p,p')
               | xs::xss =>
                   let
                     val permute = Lst.foldr
                     val x = new xs
                              $ (Lst.fsl xvec) @ (Lst.fsl xvec') @ I.Term.support n
                              @ I.Term.support n' @ support p @ support p'
                     val pi  = map (Tpl.tuple x) (Lst.fsl xvec)
                     val pi' = map (Tpl.tuple x) (Lst.fsl xvec')

                     val n   = permute I.Term.swap n pi
                     val n'  = permute I.Term.swap n' pi'
                     val p   = permute swap p pi
                     val p'  = permute swap p' pi
                   in
                     I.Term.eqData (n,n') andalso eq alphaEq (p,p')
                   end)
      | eq alphaEq (Case cs, Case cs') =
        caseEq alphaEq cs cs'
      | eq alphaEq (Restriction (a,t,p), Restriction (a',t',p')) =
        alphaEq ((a,p), (a',p'))
      | eq alphaEq (Parallel (p,q), Parallel (p',q')) =
        eq alphaEq (p,p') andalso eq alphaEq (q,q')
      | eq alphaEq (Replication p, Replication p') =
        eq alphaEq (p,p')
      | eq alphaEq (Assertion psi, Assertion psi') =
        I.Assr.eqData (psi,psi')
      | eq alphaEq (Invocation (a,mvec), Invocation (a',mvec')) =
        I.Term.eqData (a,a') andalso TVec.eqData (mvec, mvec')
      | eq alphaEq _ = false
    and caseEq alphaEq [] [] = true
      | caseEq alphaEq [] _  = false
      | caseEq alphaEq _  [] = false
      | caseEq alphaEq ((phi,p)::cs) ((phi',p')::cs') =
        I.Cond.eqData (phi,phi') andalso
        eq alphaEq (p,p') andalso
        caseEq alphaEq cs cs'

  end)

  open Nom

  structure NN = NominalName(Nom)
  structure PA = NominalAlpha(Nom)

  fun subst' _ Nil = Nil
    | subst' s (Output (m,n,p)) =
        Output (substT s m, substT s n, subst' s p)
    | subst' s (Case cases) =
        Case (map (fn (cond, p) => (substC s cond, subst' s p)) cases)
    | subst' s (Parallel (p, q)) =
        Parallel (subst' s p, subst' s q)
    | subst' s (Replication p) =
        Replication (subst' s p)
    | subst' s (Assertion a) =
        Assertion (substA s a)
    | subst' s (res as (Restriction (y,t,p))) =
        (* y # xvec, y # tvec, y # tyvec *)
        let
          val xvec  = map Tpl.fst s
          val tvec  = List.concat $ map (supportT o Tpl.snd) s
          val tyvec = supportTy t
        in
          PA.makeFresh [y] (Restriction (y,t,p)) (xvec @ tvec @ tyvec) |>
            (fn (Restriction (y,t,p)) =>
                Restriction (y,substTy s t,subst' s p) 
              | _ => Err.undefined () )
        end
    | subst' s (inp as (Input (m, xvec, n, p))) =
        (* xvec # yvec, tvec, pvec *)
        let
          val yvec  = map Tpl.fst s
          val tvec  = List.concat $ map (supportT o Tpl.snd) s
          val pvec  = support p
          val tyvec = List.concat $ map supportTy  (Lst.scl xvec)
        in
          PA.makeFresh (Lst.fsl xvec @ tyvec ) inp (yvec @ tvec @ pvec) |>
             (fn (Input (_, xvec, n, p)) =>
               Input (substT s m, xvec, substT s n, subst' s p)
               | _ => Err.undefined ())
        end
    | subst' s (Invocation (k, mvec)) =
        Invocation (k, map (substT s) mvec)

  fun subst agent sigma = subst' sigma agent

end;
