(* pi instance with assertions *)
structure PiInstanceRequirements =
struct

  type name  = string

  datatype term  = Name of name | In of name | Out of name 

  datatype d = I | O (* subtypes tags *)

  datatype condition = Eq of term * term | T | Asser of (name * d) 

  type assertion = (name * d) list (* non-trivial assertions *)

  (* types defenition for pi-instance with assertions*)
  datatype ty   
    = Base
    | Chan of ty
    | Inp of ty 
    | Outp of ty

  exception TypeErr of string 
  
  type atom = name

  fun chaneq  (a,b)        = Eq (a,b)
  fun compose (psi1,psi2)  = psi1 @ psi2
  val unit                 = []

  fun entails (psi, Eq (In a, Out b)) = 
        let val af = Lst.member (a,I) psi
            val bf = Lst.member (b,O) psi
        in
          a = b andalso af andalso bf  
        end
    | entails (psi, Eq (Out a, In b)) = 
        let val af = Lst.member (a,O) psi
            val bf = Lst.member (b,I) psi
        in
          a = b andalso af andalso bf 
        end
    | entails (psi, Eq (In a, In b)) = 
        let val af = Lst.member (a,I) psi
            val bf = Lst.member (b,I) psi
        in
          a = b andalso af andalso bf  
        end
    | entails (psi, Eq (Out a, Out b)) = 
        let val af = Lst.member (a,O) psi
            val bf = Lst.member (b,O) psi
        in
          a = b andalso af andalso bf  
        end
    | entails (psi, Eq (Name a, Name b)) = false
    | entails (psi, Eq (_, _)) = false
    | entails (psi, Asser a) = Lst.member a psi  
    | entails (_, T) = true

  fun swap_name (a,b) n = StringName.swap_name (a,b) n

  fun new _ xvec = StringName.generateDistinct xvec

  fun supportT (Name n)   = [n]
    | supportT (In n)     = [n]
    | supportT (Out n)    = [n]

  fun supportC (Eq (a, b))    = supportT a @ supportT b
    | supportC (Asser (n, d)) = [n]
    | supportC  T             = []

  fun supportA [] = [] 
    | supportA ((n,d)::xs)    = n::(supportA xs)

  (* support function for types *)
  fun supportTy _ = []

  fun swapT pi (Name n)  = Name (swap_name pi n)
    | swapT pi (In n)    = In (swap_name pi n)
    | swapT pi (Out n)   = Out (swap_name pi n)

  fun swapC _  T = T
    | swapC pi (Eq (t1, t2)) =
        Eq (swapT pi t1, swapT pi t2)
    | swapC pi (Asser (n,d)) =
        Asser(swap_name pi n,d) 
        

  fun swapA pi [] = []
    | swapA pi ((n,d)::xs)  = (swap_name pi n,d)::(swapA pi xs)

  (* swap function for types *)
  fun swapTy _ t = t

  fun eqT _ (a,b) = a = b
  fun eqC _ (a,b) = a = b
  fun eqA _ (psi,psi') = 
    Lst.all (fn a => Lst.member a psi') psi andalso
    Lst.all (fn a => Lst.member a psi ) psi' 

  (* equality for types *)
  fun eqTy _ (a,b) = a = b

  fun substT sigma (Name n) = 
        (case List.find (fn (x,_) => x = n) sigma of
           NONE       => Name n
         | SOME (_,t) => t)
    | substT sigma (In n) = 
        (case List.find (fn (x,_) => x = n) sigma of
           NONE       => In n
         | SOME (_,Name n') => In n' 
	 | _  => raise TypeErr "Incompatible substitution!")
    | substT sigma (Out n) = 
        (case List.find (fn (x,_) => x = n) sigma of
           NONE       => Out n
         | SOME (_,Name n') => Out n'
         | _ => raise TypeErr "Incompatible substitution!")
  
  fun substC sigma T             = T
    | substC sigma (Eq (t1, t2)) =
        Eq (substT sigma t1, substT sigma t2)
    | substC sigma (Asser (n,I)) =
        (case substT sigma (Name n) of
            Name n => Asser(n,I)
          | _ => raise TypeErr "Incompatible substitution!")
    | substC sigma (Asser (n,O)) =
        (case substT sigma (Name n) of 
            Name n => Asser(n,O)
          | _ => raise TypeErr "Incompatible substitution!")

  (* substitution function for assertions *)
  fun substA sigma psi =
     map (fn (n,d) =>
            case List.find (fn (a,b) => a = n) sigma of 
              NONE => (n,d) 
            | SOME (_,(Name n')) => (n',d)
            | _ => raise TypeErr "Incompatible substitution!") psi

  (* substitution function for types *)
  fun substTy _ t = t

  (* pi-calculus is unsorted *)
  structure Sort = Unsorted

  fun isNameSort _ = true
  fun canRecv _ _  = true
  fun canSend _ _  = true
  fun canSubs _ _  = true
  fun nameSort _   = Unsorted.SORT
  fun sortT _      = Unsorted.SORT
  fun sortC _      = Unsorted.SORT
  fun sortA _      = Unsorted.SORT
  fun sortTy _     = Unsorted.SORT 

  structure Term = Nominal(struct
    structure AtomSort = Sort
    structure DataSort = Sort
    type atom    = name
    type data    = term
    val atomSort = nameSort
    val dataSort = sortT
    val swap     = swapT
    val support  = supportT
    val eq       = eqT
    val new      = new
  end)

  structure Cond = Nominal(struct
    structure AtomSort = Sort
    structure DataSort = Sort
    type atom    = name
    type data    = condition
    val atomSort = nameSort
    val dataSort = sortC
    val swap     = swapC
    val support  = supportC
    val eq       = eqC
    val new      = new
  end)

  structure Assr = Nominal(struct
    structure AtomSort = Sort
    structure DataSort = Sort
    type atom    = name
    type data    = assertion
    val atomSort = nameSort
    val dataSort = sortA
    val swap     = swapA
    val support  = supportA
    val eq       = eqA
    val new      = new
  end)

  structure Type = Nominal(struct
    structure AtomSort = Sort
    structure DataSort = Sort
    type atom = name
    type data = ty
    val atomSort = nameSort
    val dataSort = sortTy
    val swap     = swapTy
    val support  = supportTy
    val eq       = eqTy 
    val new      = new
  end)

  (* type environment for pi-instance with assertions *)
  structure Env = TypeEnv(struct
    structure Assr = Assr
    structure Type = Type
    val unitAssr = []
    fun compose psiE psi = psiE @ psi
  end)

  (* Type-checker's functions required by pi instance 
   * these functions are instance specific and will
   * differ from instance to instance. *)

  fun compatIn  _ Us Uo = (Us = Inp(Uo))

  fun compatOut _ Ts To = (Ts = Outp(To))

  open Missing;

  fun checkT e (Name n) = 
        (case Env.find e n of 
           SOME ty => ty 
         | NONE => raise TypeErr 
                   ("Err: The name " ^n^ 
                    " is not defined in the type environment!"))
    (*   E |-- M : Ch(T)   M^i \in PsiE
	 * --------------------------------
	 *   E |-- In(M) : Inp(T)
     *) 
    | checkT e (In m) = 
        (case checkT e (Name m) of 
           Chan(t) => 
             if Lst.member (m,I) (Env.getAssr e) then Inp(t) 
             else raise TypeErr ("Err: Assertion ("^m^
                                 ",i) is not present in the type environment!")
         | _ => 
             raise TypeErr ("Err: The name "^m^" has the wrong type "^
			                "(not a Chan type) in the type environment!"))
    | checkT e (Out m) = 
        (case checkT e (Name m) of 
           Chan(t) => 
             if Lst.member (m,O) (Env.getAssr e) then Outp(t) 
             else raise TypeErr ("Err: Assertion ("^m^
                                 ",o) is not present in the type environment!")
         | _ => 
             raise TypeErr ("Err: The name "^m^" has the wrong type "^ 
                            "(not a Chan type) in the type environment!"))

  fun checkAbs e xtvec _ =
    case xtvec of
      [(_,t)] => t
    | _ => raise TypeErr
           ("Err: Mall-formed input pattern!") (* Improve error message *)

  fun checkC e c = 
    case c of 
      (* 
	   *   E |-- M : Ch(T) 
	   * -----------------
	   *    E |-- M^d
	   *)
      Asser (n,_) => 
        (case checkT e (Name n) of
            Chan(_) => ()
          | _ => raise TypeErr ("Err: Condition type error!"))
      (*     
       *     E |-- a^i   E |-- b^o
       * -----------------------------
       *     E |-- Eq (In(a),Out(b))
       *)
    | Eq (In(a),Out(b)) =>
        let val mt  = checkC e (Asser (a,I)) 
            val nt  = checkC e (Asser (b,O)) 
        in
          ()
        end
      (*     
       *     E |-- a^o   E |-- b^i
       * -----------------------------
       *     E |-- Eq (Out(a),In(b))
       *)
    | Eq (Out(a),In(b)) =>
        let val mt  = checkC e (Asser (a,O)) 
            val nt  = checkC e (Asser (b,I)) 
        in
          ()
        end
      (*     
       *     E |-- a^o   E |-- b^i
       * -----------------------------
       *     E |-- Eq (Out(a),In(b))
       *)

    | Eq (Name a,Name b) => 
        let val at  = checkT e (Name a) 
            val bt  = checkT e (Name b) 
        in
          if at = bt then () else raise TypeErr ("Err: Condition type error!")
        end
    | Eq (_,_) => raise TypeErr ("Err: Condition type error!")

    | T => ()

  (* 
   *   E |-- ai : Ch(T)  1 <= i <= n  d in {I,O} 
   *   -----------------------------------------
   *       E |-- {(a1,d),(a2,d),...,(an,d)}
   *)
  fun checkA e psi =	
    if (List.all 
       (fn (n,d) => 
         case checkT e (Name n) of
           Chan(_) => true
         | _ => (print("\nErr: The name "^n^
                       " has a malformed type"^ 
                       " regarding the assertion ("^n^",i/o)"); false))
       psi) 
    then ()  
    else raise TypeErr ("\nErr: Could not type-check the assertion agent!")
end;

structure PsiPiInstance = Psi(PiInstanceRequirements)

structure PiSymbolicInstanceRequirements =
struct

  open PiInstanceRequirements

  fun var (x,t) = (Name x)

  fun var' x = (Name x)

  structure Constraint = SymbolicOSConstraint(PsiPiInstance.Inst)


  fun dom sigma = map (fn (n,t) => n) sigma

  fun composeSubst sigma (s as (x',l')) =
  let
    val app = map (fn (n,t) => (n, substT [s] t)) sigma
  in
    if Lst.member x' (dom sigma)
      then app
      else s :: app
  end

  structure L = NominalNameList(PsiPiInstance.Inst.Term)
      (* struct type atom = name val new = new end) *)

  fun freshL avec bvec =
    List.all (fn b => L.fresh b avec) bvec

  (* transition constraint solver for pi with I/O assertions *)
  fun mgu e [] (sigma, psi') = Either.RIGHT (sigma, psi')
    | mgu e ((avec, psi, T)::cs) (sigma, psi') =
      mgu e cs (sigma, psi')

    | mgu e ((avec, psi, (Asser(n,d)))::cs) (sigma, psi') = 
        if (Lst.member (n,d) psi') orelse
           ((L.fresh n (Lst.fsl avec)) andalso 
             (Lst.member (n,d) psi)) 
        then 
          mgu e cs (sigma, psi') 
        else 
          if (L.fresh n (Lst.fsl avec)) andalso 
             not (Lst.member (n,d) (compose (psi,psi'))) 
          then mgu e cs (sigma, psi') 
        else 
          let val m = L.new n (Lst.fsl avec) 
          in 
            if (L.fresh n (Lst.fsl avec)) andalso 
               (Lst.member (m,d) (compose (psi,psi')))
            then mgu e cs
                ((composeSubst sigma (n, Name m)), psi')
            else Either.LEFT [(Asser(n,d))]       
          end   

    | mgu e ((avec, psi, (Eq(In a, Out b)))::cs) (sigma, psi') =
        if a = b andalso (Lst.member a (Lst.fsl avec)) 
                 andalso (Lst.member (a,I) psi) 
                 andalso (Lst.member (a,O) psi)  
        then mgu e cs (sigma, psi') 
        else
        if 
          (L.fresh a (Lst.fsl avec)) andalso 
          (L.fresh b (Lst.fsl avec)) andalso 
          (Lst.member (a,I) psi)     orelse 
          (Lst.member (a,O) psi) 
        then mgu e (Constraint.subst cs [(a, Name b)])
                   ((composeSubst sigma (a, Name b)), psi')
        else 
        if
          (L.fresh a (Lst.fsl avec)) andalso 
          (L.fresh b (Lst.fsl avec)) andalso 
          not (Lst.member (a,I) psi) andalso 
          not (Lst.member (a,O) psi) 
        then mgu e (Constraint.subst cs [(a, Name b)])
                   ((composeSubst sigma (a, Name b)), 
                    compose (psi', [(b,I),(b,O)]))
        else Either.LEFT [(Eq(In a, Out b))]

    | mgu e ((avec, psi, con as (Eq(In a, Name b)))::cs) (sigma, psi') =
        if L.fresh a (Lst.fsl avec) andalso 
           L.fresh b (Lst.fsl avec) andalso
           Lst.member (a,I) psi     orelse 
           Lst.member (a,O) psi      
        then mgu e (Constraint.subst cs [(b, Out a)])
                   ((composeSubst sigma (b, Out a)), psi')
        else 
        if L.fresh a (Lst.fsl avec)   andalso 
           L.fresh b (Lst.fsl avec)   andalso
           not (Lst.member (a,I) psi) orelse 
           not (Lst.member (a,O) psi)      
        then mgu e (Constraint.subst cs [(b, Out a)])
                   ((composeSubst sigma (b, Out a)), compose (psi',[(a,O),(a,I)]))
        else Either.LEFT [con]

    | mgu e ((avec, psi, con as (Eq(Out a, Name b)))::cs) (sigma, psi') =
        if L.fresh a (Lst.fsl avec) andalso 
           L.fresh b (Lst.fsl avec) andalso
           Lst.member (a,I) psi     orelse 
           Lst.member (a,O) psi      
        then mgu e (Constraint.subst cs [(b, In a)])
                   ((composeSubst sigma (b, In a)), psi')
        else
        if L.fresh a (Lst.fsl avec)   andalso 
           L.fresh b (Lst.fsl avec)   andalso
           not (Lst.member (a,I) psi) orelse 
           not (Lst.member (a,O) psi)      
        then mgu e (Constraint.subst cs [(b, In a)])
                   ((composeSubst sigma (b, In a)), compose (psi',[(a,O),(a,I)]))
        else Either.LEFT [con]

    | mgu e ((avec, psi, con as (Eq(Name a, Name b)))::cs) (sigma, psi') =
       if L.fresh a (Lst.fsl avec) andalso
          L.fresh b (Lst.fsl avec)
       then 
         let val c = L.new a (Lst.fsl avec)
         in  
           if L.fresh c (Assr.support psi)  andalso
              L.fresh c (Assr.support psi') andalso
              L.fresh c (Lst.fsl avec) 
           then 
             let 
                val sigma' = composeSubst sigma (a, In c)
             in mgu e (Constraint.subst cs [(a, In c),(b, Out c)])
                      ((composeSubst sigma' (b, Out c)), psi')
             end
           else Either.LEFT [con]
         end
       else Either.LEFT [con]
            
    | mgu e ((avec, psi, con as (Eq(_,_)))::cs) (sigma, psi') =
         Either.LEFT [con]  


  fun solve e cs =
    case mgu e cs ([],[]) of
         Either.RIGHT (sigma, psi') => Either.RIGHT [(sigma, psi')]
       | Either.LEFT phi => Either.LEFT  [phi]
 

  structure BisimConstraint = SymBisimConstraint(PsiPiInstance)
  
  val solveBisim = NONE
  fun nameOfConstrSort () = "a"

end;

structure SymbolicInstance : SYMBOLIC_PSI = struct
  structure Psi         = PsiPiInstance
  structure Clause      = PsiClause(Psi)
  structure ClEnv       = PsiClauseEnvironment(Clause)
  structure PsiInstance = PsiPiInstance.Inst
  structure Constraint  = PiSymbolicInstanceRequirements.Constraint
  val var               = PiSymbolicInstanceRequirements.var'
  val nameOfConstrSort  = PiSymbolicInstanceRequirements.nameOfConstrSort
end


structure SymbolicConstraintSolver : SYMBOLIC_CONSTRAINT_SOLVER =
struct
  structure Inst       = PsiPiInstance.Inst
  structure Constraint = PiSymbolicInstanceRequirements.Constraint
  val solve            = PiSymbolicInstanceRequirements.solve
end;

structure SymbolicBisimConstraintSolver : SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
struct
  structure Psi = PsiPiInstance
  structure Constraint = PiSymbolicInstanceRequirements.BisimConstraint
  val solve =
    case PiSymbolicInstanceRequirements.solveBisim of
         NONE => (fn pp => fn c => Either.LEFT [])
       | SOME s => s
end;

structure PiParserPrinterRequirements =
struct

  open PiInstanceRequirements

  fun printN a = a
  fun printT (Name a) = a
    | printT (In a)   = "In( " ^ a ^" )"
    | printT (Out a)  = "Out( " ^ a ^" )"

  fun printC (Eq (a, b)) = (printT a) ^ " <-> " ^ (printT b)
    | printC  T = "T"
    | printC (Asser(n,d)) = 
        case d of 
          I => n ^ "^" ^ "i"
        | O => n ^ "^" ^ "o"
                             
  fun printA psi = String.concat (map (fn (n,d) => " (" ^ n ^ "^" ^ printD d ^ ") ") psi)
  and printD I = "i"
    | printD O = "o"

  (* printing the types *)
  fun printTy (Base)   = "Base"
    | printTy (Chan t) = "Ch(" ^ printTy t ^ ")"
    | printTy (Inp t)  = "Inp(" ^ printTy t ^ ")"
    | printTy (Outp t) = "Outp(" ^ printTy t ^ ")"

  structure Parser = Parser(StringStream)
  structure Lex = PsiParserBase(Parser)

  fun p >>= q = Parser.>>= (p,q)
  fun p >>  q = Parser.>>  (p,q)

  val name = Lex.identifier


  fun term () =
        (Lex.stok "In" >> Lex.stok "(" >>
         name  >>=
        (fn n => Lex.stok ")" >> Parser.return (In n)))
    </Parser.choice/>
        (Lex.stok "Out" >> Lex.stok "(" >>
         name  >>=
        (fn n => Lex.stok ")" >> Parser.return (Out n)))
    </Parser.choice/>
       (Lex.identifier >>= Parser.return o Name)
 
  fun d () = 
     (Lex.stok "I" >>=
     (fn i => Parser.return (I)))
     </Parser.choice/> 
     (Lex.stok "O" >>=
     (fn i => Parser.return (O)))


  val condEq =  term () >>=
    (fn a =>    Lex.stok "=" >>
                term () >>=
    (fn b =>    Parser.return (Eq (a,b))
    ))

  val condAss = name >>=
    (fn n =>    Lex.stok "=" >>
                d () >>=
    (fn d =>    Parser.return (Asser (n,d))
    ))

  val cond = Parser.choice (condAss, condEq)

  fun ass () = Lex.stok "(" >> name >>=
                (fn n => Lex.stok "," >> d () >>=
                (fn d => Lex.stok ")" >> Parser.return (n,d)))

  fun assr () = (Parser.delayed ass) </Parser.sepby/> Lex.stok "," >>=
                (fn al => Parser.return al)
 
  fun typ () = 
        (Lex.stok "Base" >> Parser.return Base)                   
        </Parser.choice/>
        (Lex.stok "Ch" >> Lex.stok "(" >>
        (Parser.delayed typ) >>= 
        (fn t => Lex.stok ")" >> Parser.return (Chan t)))
        </Parser.choice/>
        (Lex.stok "Inp" >> Lex.stok "(" >>
        (Parser.delayed typ) >>= 
        (fn t => Lex.stok ")" >> Parser.return (Inp t)))
        </Parser.choice/>
        (Lex.stok "Outp" >> Lex.stok "(" >>
        (Parser.delayed typ) >>= 
        (fn t => Lex.stok ")" >> Parser.return (Outp t)))

  fun parseResult p s =
    case Parser.parse p (StringStream.make s) of
         Either.RIGHT [(r,s)] => Either.RIGHT r
       | Either.RIGHT _ => Err.undefined ()
       | Either.LEFT  _ => Either.LEFT "Error parsing"

  fun parseName s   = parseResult name s
  fun parseTerm s   = parseResult (term ()) s
  fun parseCond s   = parseResult cond s
  fun parseAssr s   = parseResult (assr ()) s
  fun parseTy   s   = parseResult (typ ()) s

end;

structure PiParserRequirements : PSI_PARSER_REQ =
struct
  structure Psi = PsiPiInstance
  open PiParserPrinterRequirements
  val var = SOME PiSymbolicInstanceRequirements.var
end;

structure PiPrinterRequirements : PSI_INSTANCE_PRETTY_PRINTER =
struct
  structure Inst = PsiPiInstance.Inst
  open PiParserPrinterRequirements
  val var = SOME PiSymbolicInstanceRequirements.var
end;

structure PiCommand = CommandParser(struct
  structure SI           = SymbolicInstance
  structure SCS          = SymbolicConstraintSolver
  structure SBCS         = SymbolicBisimConstraintSolver
  structure PsiParserReq = PiParserRequirements
  structure PPInst       = PiPrinterRequirements
  val useBisim           = true
end);


structure APi = PiCommand;

