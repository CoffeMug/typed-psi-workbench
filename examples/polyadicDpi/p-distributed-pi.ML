(* distributed-pi instance *)
structure DPiInstanceRequirements =
struct

  type name          = string
  datatype term      = Name of name
                     | LocationName of name * name
                     | Tup of term list (* polyadic terms *)
 
  datatype condition = Eq of term * term | True
  type assertion     = unit

  (* Types for distributed-pi instance *)
  datatype ty = Chan of ty 
              | Location of name list 
              | TupTy of ty list (* polyadic dpi *)
              | Base

  (* Type environment for distributed-pi instance *)
  structure Env = TypeEnv(struct
    type key     = name
    type value   = ty
    type asser   = assertion
    val unitAssr = ()
    fun compose _ _ = ()
  end)

  exception TypeErr of string

  type atom = name

  fun chaneq (a,b)        = Eq (a,b)
  fun compose (psi1,psi2) = ()
  val unit = ()

  fun entails (_,Eq(m,n)) = m = n
    | entails (_,True)    = true
 
  fun swap_name (a,b) n =  StringName.swap_name (a,b) n

  fun new _ xvec = StringName.generateDistinct xvec

  fun supportT (LocationName(n1,n2)) = [n1,n2]
    | supportT (Name n) = [n]
    | supportT (Tup tl) = List.concat (map supportT tl) 

  fun supportC (Eq (a, b)) = supportT a @ supportT b
    | supportC True = []

  fun supportA _  = []

  (* Support function for types *)
  fun supportTy (Chan t)      = supportTy t
    | supportTy (Location nl) = nl
    | supportTy (TupTy tyl)   = List.concat (map supportTy tyl)
    | supportTy (Base)        = [] 

  fun swapT pi (LocationName(n1,n2)) = 
        LocationName(swap_name pi n1, swap_name pi n2)
    | swapT pi (Tup tl) = Tup (map (swapT pi) tl) 
    | swapT pi (Name n) = Name (swap_name pi n)

  fun swapC pi (Eq(t1,t2)) = Eq(swapT pi t1,swapT pi t2)
    | swapC _ True         = True

  fun swapA _ _ = ()

  (* Swap function for types *)
  fun swapTy pi (Chan(t))     = Chan(swapTy pi t)
    | swapTy pi (Location(l)) = Location (map (swap_name pi) l)
    | swapTy pi (TupTy(tyl))  = TupTy (map (swapTy pi) tyl)
    | swapTy pi (Base)        = Base    

  fun eqT _ (a,b) = a = b
  fun eqC _ (a,b) = a = b
  fun eqA _ (a,b) = a = b 

  (* Equality for types *)
  fun eqTy _ ((Location al), (Location bl)) = 
        (List.length al = List.length bl) 
    | eqTy _ (a,b) = a = b 

  fun substT sigma (LocationName(n1,n2)) =
    let val s1 = case substT sigma (Name n1) of 
                   Name n => n 
                 | _ => raise TypeErr "mallformed susbstitution!"
        val s2 = case substT sigma (Name n2) of
                   Name n => n
                 | _ => raise TypeErr "mallformed susbstitution!"
    in
      LocationName (s1,s2)
    end
    | substT sigma (Tup tl) = 
        Tup (map (substT sigma) tl)         

    | substT sigma (Name a) =
        (case List.find (fn (b,_) => a = b) sigma of
           NONE       => Name a
         | SOME (_,t) => t)

  fun substC sigma (Eq (t1, t2)) =
        Eq (substT sigma t1, substT sigma t2)
    | substC _ True = True

  fun substA sigma () = ()

  (* Substitution function for types *)
  fun substTy sigma (Chan(t))      = Chan(substTy sigma t)
    | substTy sigma (Location(nl)) = Location (map (substN sigma) nl)
    | substTy sigma (TupTy(tyl))   = TupTy (map (substTy sigma) tyl) 
    | substTy sigma (Base)         = Base
  and substN sigma n = case substT sigma (Name n) of
                         Name n' => n'
                       | _ => raise TypeErr "mallformed susbstitution!"


  (* sorting requirements *)
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


  (* Type-checker's functions required
   * by distributed-pi instance. These functions
   * are instance specific and differ from instance
   * to instance. *)
    
  fun compatIn e Us Uo = (Us = Chan(Uo)) 

  fun compatOut e Ts To = (Ts = Chan(To)) 


  open Missing;

  fun checkT e (LocationName(l,a)) = checkCompositT e (l,a)
    | checkT e (Tup tl) = TupTy(map (checkT e) tl)   
    | checkT e (Name n) = 
        (case Env.find e n of 
           SOME ty => ty 
         | NONE => raise TypeErr 
           ("Err: The name "^ n ^" is not defined in the type environment!"))

  (* Implementation of the type checking 
   * rule for the composite terms of Dpi-calculus.
   * 
   * E |-- l : Loc { a }    E |-- a : Ch(T)   
   * ---------------------------------------------
   *             E |-- l.a : Ch(T) 
   *                                                                      
   ***********************************************)
  and checkCompositT e (l,a) = 
    let val Tl = checkT e (Name l)
        val Ta = checkT e (Name a) 
    in
      case Tl of 
        Location(nls) => 
          if (member a nls) then 
            (case Ta of
              (Chan t) => (Chan t)
             | _     => raise TypeErr ("Err: Bad type for Channel " ^ a ^ 
                                      " at location " ^ l ^ "!")) 
          else raise TypeErr ("Err: Channel " ^ a ^ 
                              " is not defined in the interface of location " ^ l ^ "!") 
      | _ => raise TypeErr ("Err: Name " ^ l ^ 
                            " has a mallformed type; expected location type!") 
    end     

  fun checkAbs e xvec n =
    case n of 
      (Tup tl) => 
         let val nt = checkT e n
         in 
           case nt of 
             (TupTy (tyl)) => 
                if ((map Tpl.snd xvec) = tyl) then
                  nt
                else raise TypeErr ("Err: Pattern matching rule error!")
           | _ => raise TypeErr ("Err: Bad type for tuple!")
         end
    | _ => 
      (case xvec of 
         [(_,t)] => t
       | _ => raise TypeErr ("Err: Pattern matching rule error!"))  

  fun checkC e (Eq(a,b)) = 
    let 
      val t1 = checkT e a
      val t2 = checkT e b
    in   
      if (t1 = t2) then ()
      else raise TypeErr ("Err: Condition type error!")
    end
    | checkC e True = ()

  fun checkA e a = ()

end;


structure PsiDPiInstance = Psi(DPiInstanceRequirements) 

structure DPiSymbolicInstanceRequirements =
struct

  open DPiInstanceRequirements

  fun var (x,t) = LocationName(x,x)

  fun var' a  = Name a

  structure Constraint = SymbolicOSConstraint(PsiDPiInstance.Inst)

  fun dom sigma = map (fn (n,t) => n) sigma

  fun composeSubst sigma (s as (x',l')) =
  let
    val app = map (fn (n,t) => (n, substT [s] t)) sigma
  in
    if Lst.member x' (dom sigma)
      then app
      else s :: app
  end

  structure L = NominalNameList(PsiDPiInstance.Inst.Term)
      (* struct type atom = name val new = new end) *)

  fun freshL avec bvec =
    List.all (fn b => L.fresh b avec) bvec

  fun mgu [] sigma = Either.RIGHT sigma
      
    | mgu ((avec, (),  True )::cs) sigma = mgu cs sigma                      

    | mgu ((avec, (), (con as Eq (LocationName(l,a), la' as LocationName(l',a'))))::cs) sigma =
        if l = l' andalso a = a' then mgu cs sigma
          else
            let val af  = L.fresh a (Lst.fsl avec)
                val lf  = L.fresh l (Lst.fsl avec)
                val fls = freshL (Lst.fsl avec) (supportT la')
            in
              if af andalso lf andalso fls then
                let val compSub = composeSubst sigma (l, Name l')
                in
                   mgu (Constraint.subst cs [(a , Name a'),(l, Name l')])
                  (composeSubst compSub (a, Name a'))
                end
              else Either.LEFT [con]
            end

    | mgu ((avec, (), (con as Eq (Name a, Name a')))::cs) sigma = 
        if a = a' then mgu cs sigma
          else 
            if L.fresh a (Lst.fsl avec) then 
              mgu (Constraint.subst cs [(a, Name a')])
                  (composeSubst sigma (a, Name a'))
            else 
              Either.LEFT [con]

    | mgu ((avec, (), (con as Eq (LocationName (l,a), Name a')))::cs) sigma = 
        if a = a' then mgu cs sigma
        else 
          if L.fresh a (Lst.fsl avec) then 
            mgu (Constraint.subst cs [(a, Name a')])
                (composeSubst sigma (a, Name a'))
          else Either.LEFT [con]

    | mgu ((avec, (), (con as Eq (_,_)))::cs) sigma =
        Either.LEFT [con]  

  fun solve cs =
    case mgu cs [] of
         Either.RIGHT sigma => Either.RIGHT [(sigma, ())]
       | Either.LEFT phi    => Either.LEFT  [phi]

  structure BisimConstraint = SymBisimConstraint(PsiDPiInstance)
  (* skip *)
  
  val solveBisim = NONE
  fun nameOfConstrSort () = "a"

end;

structure SymbolicInstance : SYMBOLIC_PSI = struct
  structure Psi         = PsiDPiInstance
  structure Clause      = PsiClause(Psi)
  structure ClEnv       = PsiClauseEnvironment(Clause)
  structure PsiInstance = PsiDPiInstance.Inst
  structure Constraint  = DPiSymbolicInstanceRequirements.Constraint
  val var               = DPiSymbolicInstanceRequirements.var'
  val nameOfConstrSort  = DPiSymbolicInstanceRequirements.nameOfConstrSort
end


structure SymbolicConstraintSolver : SYMBOLIC_CONSTRAINT_SOLVER =
struct
  structure Inst       = PsiDPiInstance.Inst
  structure Constraint = DPiSymbolicInstanceRequirements.Constraint
  val solve            = DPiSymbolicInstanceRequirements.solve
end;

structure SymbolicBisimConstraintSolver : SYMBOLIC_BISIM_CONSTRAINT_SOLVER =
struct
  structure Psi = PsiDPiInstance
  structure Constraint = DPiSymbolicInstanceRequirements.BisimConstraint
  val solve =
    case DPiSymbolicInstanceRequirements.solveBisim of
         NONE => (fn pp => fn c => Either.LEFT [])
       | SOME s => s
end;

structure DPiParserPrinterRequirements =
struct

  open DPiInstanceRequirements

  fun printN a = a

  fun printT (LocationName(l,a)) = (printN a) ^ "@" ^ (printN l)
    | printT (Tup tl) = "{" ^ printTList tl 
    | printT (Name n) = n
  and printTList [] = ""
    | printTList (t::[]) = printT t ^ "}" 
    | printTList (t::xs) = printT t ^ "," ^ printTList xs

  fun printC (Eq (a, b)) = (printT a) ^ " = " ^ (printT b)
    | printC True = "T"

  fun printA psi = "1"

  (* printing the types *)
  fun printTy (Base)       = "Base"
    | printTy (Chan t)     = "Ch(" ^ printTy t ^ ")"
    | printTy (Location nl) = "Loc { " ^ printNList nl
    | printTy (TupTy tyl)  = "{" ^ printTyList tyl
  and printNList [] = ""
    | printNList (n::[]) = n ^ " }" 
    | printNList (n::xs) = n ^ "," ^ printNList xs
  and printTyList [] = ""
    | printTyList (ty::[]) = printTy ty ^ "}"  
    | printTyList (ty::xs) = printTy ty ^ "," ^ printTyList xs  

  structure Parser = Parser(StringStream)
  structure Lex = PsiParserBase(Parser)

  fun p >>= q = Parser.>>= (p,q)
  fun p >>  q = Parser.>>  (p,q)

  val name = Lex.identifier

  val condEq =  name >>=
    (fn l =>    name >>= 
    (fn a =>    Lex.stok "=" >>
                name >>=
    (fn l' =>   name >>= 
    (fn a' =>   Parser.return (Eq (LocationName(l,a),LocationName(l',a')))
    ))))

  val cond = condEq </Parser.choice/> (Lex.stok "T" >> Parser.return True)

  val assr = Lex.stok "1" >> Parser.return ()

  (* Parsing the structured terms of Dpi instance. *)
  fun term () = 
        (Lex.stok "loChan" >> Lex.stok "(" >>
         name >>= 
        (fn n1 => Lex.stok "," >>
         name >>= 
        (fn n2 => Lex.stok ")" >> Parser.return (LocationName(n1,n2))
        )))
     </Parser.choice/> 
         (Lex.stok "Tup" >> Lex.stok "[" >> ((Parser.delayed term) 
          </Parser.sepby/> (Lex.stok ",")) >>=
         (fn tl => Lex.stok "]" >> 
          Parser.return (Tup(tl))))
     </Parser.choice/>
        (Lex.identifier >>= Parser.return o Name)
 
  fun typ () = 
        (Lex.stok "Base" >> Parser.return Base)                   
      </Parser.choice/>
        (Lex.stok "Loc" >> Lex.stok "{" >>
        ((name) </Parser.sepby/> (Lex.stok ",")) >>=
        (fn nl => Lex.stok "}" >> Parser.return (Location(nl))))
      </Parser.choice/>
        (Lex.stok "Ch(" >>
        (Parser.delayed typ) >>= 
        (fn t => Lex.stok ")" >> Parser.return (Chan t)))
      </Parser.choice/> 
        (Lex.stok "[" >>
        ((Parser.delayed typ) </Parser.sepby/> (Lex.stok ",")) >>=
        (fn tyl => Lex.stok "]" >> Parser.return (TupTy(tyl))))   
 

  fun parseResult p s =
    case Parser.parse p (StringStream.make s) of
         Either.RIGHT [(r,s)] => Either.RIGHT r
       | Either.RIGHT _ => Err.undefined ()
       | Either.LEFT  _ => Either.LEFT "Error parsing"

  fun parseName s = parseResult name s
  fun parseTerm s = parseResult (term ()) s
  fun parseCond s = parseResult cond s
  fun parseAssr s = parseResult assr s
  fun parseTy   s = parseResult (typ ()) s   

end;

structure DPiParserRequirements : PSI_PARSER_REQ =
struct
  structure Psi = PsiDPiInstance
  open DPiParserPrinterRequirements
  val var = SOME DPiSymbolicInstanceRequirements.var
end;

structure DPiPrinterRequirements : PSI_INSTANCE_PRETTY_PRINTER =
struct
  structure Inst = PsiDPiInstance.Inst
  open DPiParserPrinterRequirements
  val var = SOME DPiSymbolicInstanceRequirements.var
end;

structure DPiCommand = CommandParser(struct
  structure SI           = SymbolicInstance
  structure SCS          = SymbolicConstraintSolver
  structure SBCS         = SymbolicBisimConstraintSolver
  structure PsiParserReq = DPiParserRequirements
  structure PPInst       = DPiPrinterRequirements
  val useBisim           = true
end);


structure PDPi = DPiCommand;

