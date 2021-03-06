(* uses missing
     /parser
     /pp
     /psi
     /psi-parsing
     /pp-nom
     /pp-psi
     /pp-sim
     /simulator
     /bisim
     /cr
*)

signature PSI_COMMAND_INTERPRETER =
sig
  val start : unit -> unit
end;


functor CommandParser(A: sig
  structure SI           : SYMBOLIC_PSI
  structure SCS          : SYMBOLIC_CONSTRAINT_SOLVER
  structure SBCS         : SYMBOLIC_BISIM_CONSTRAINT_SOLVER
  structure PsiParserReq : PSI_PARSER_REQ
  structure PPInst       : PSI_INSTANCE_PRETTY_PRINTER
  val useBisim : bool

  sharing PsiParserReq.Psi = SI.Psi = SBCS.Psi
  sharing SI.Psi.Inst = SCS.Inst = SBCS.Psi.Inst = PPInst.Inst
  sharing SCS.Constraint.Inst = SBCS.Constraint.Psi.Inst
  sharing SCS.Constraint.AtomSort = SBCS.Constraint.AtomSort = SI.Psi.Inst.Sort

end) : PSI_COMMAND_INTERPRETER  =
struct
  open Missing
  open A


  structure Psi = SI.Psi
  structure Cl = SI.ClEnv.Cl
  structure Guarded = PsiGuarded(SI)
  structure PP = WPrettyPrinter
  structure PsiPP = PrettyPrintPsi(struct
    structure PP     = PP
    structure Psi    = Psi
    structure PPInst = PPInst
  end)
  structure PPNomPsi = PPNominal(struct
    structure PP = PP
    structure Nom = Psi
    val ppAtom = PsiPP.n
  end)
  structure PPClause = PPClause(struct
    structure PP    = PP
    structure Cl    = Cl
    structure PPPsi = PsiPP
  end)
  structure PsiParser = PsiParser(struct
    structure Parser = Parser(ParserStreamIO)
    structure Req    = PsiParserReq
  end)
  structure PsiB = PsiParserBase(PsiParser.Parser)
  structure Env  = SI.ClEnv
  structure TyEnv = Psi.Inst.Env 
  structure Sim  = SymbolicPsiSimulator(SI)
  structure WSim = WeakSymbolicPsiSimulator(SI)
  structure Bisim = Bisim(struct
    structure WSim = WSim
    structure C = SBCS.Constraint
    structure SymPsi = SI
  end)
  structure PPSAct = PPStrongAction(struct
    structure PP     = PP
    structure Act    = Sim.Tr.Act
    structure PPInst = PPInst
  end)
  open PsiParser
  open PsiParser.Parser
  open PsiB

  structure TypeChecker = TypeChecker(struct 
    structure Fr    = Frame(Psi)
    structure ClEnv = Env
  end)

  (* New fields added to the command_state record to support the typing requirements. 
   * tyenv is used for keeping track of type environment.
   * malt is used for checking the welltypedness of an agent. 
   * Appropriate functions also added here! *)
  datatype command_state = CommandState of
     { env         : Env.env
     , tyenv       : TyEnv.env
     , interactive : bool
     , width       : int
     , eof         : bool
     , malt        : bool 
     }

  fun updateEnv (CommandState {env,tyenv,interactive,width,eof,malt}) f =
    CommandState
    { env         = f env
    , tyenv       = tyenv
    , interactive = interactive
    , width       = width
    , eof         = eof
    , malt        = malt
    }

  fun updateTyEnv (CommandState {env,tyenv,interactive,width,eof,malt}) f =
    CommandState
    { env         = env
    , tyenv       = f tyenv
    , interactive = interactive
    , width       = width
    , eof         = eof
    , malt        = malt
    }

  fun resetTyEnv (CommandState {env,tyenv,interactive,width,eof,malt}) e =
    CommandState
    { env         = env
    , tyenv       = e
    , interactive = interactive
    , width       = width
    , eof         = eof
    , malt        = malt
    }



  fun getEnv (CommandState {env, ...}) = env
  fun getTyEnv (CommandState {tyenv, ...}) = tyenv

  fun getMalformedTy (CommandState {malt, ...}) = malt
  fun setEof (CommandState {env,tyenv,interactive,width,eof,malt}) =
    CommandState
    { env         = env
    , tyenv       = tyenv
    , interactive = interactive
    , width       = width
    , eof         = true
    , malt        = malt
    }
  fun setMalformedTy (CommandState {env,tyenv,interactive,width,eof,malt}) =
    CommandState
    { env         = env
    , tyenv       = tyenv
    , interactive = interactive
    , width       = width
    , eof         = eof
    , malt        = true
    }
  fun unSetMalformedTy (CommandState {env,tyenv,interactive,width,eof,malt}) =
    CommandState
    { env         = env
    , tyenv       = tyenv
    , interactive = interactive
    , width       = width
    , eof         = eof
    , malt        = false
    }


  fun unsetEof (CommandState {env,tyenv,interactive,width,eof,malt}) =
    CommandState
    { env         = env
    , tyenv       = tyenv
    , interactive = interactive
    , width       = width
    , eof         = false
    , malt        = malt
    }
  fun setStatement (CommandState {env,tyenv,interactive,width,eof,malt}) st =
    CommandState
    { env         = env
    , tyenv       = tyenv
    , interactive = interactive
    , width       = width
    , eof         = false
    , malt        = malt
    }


  fun isEof (CommandState {eof,...}) = eof
  fun getWidth (CommandState {width,...}) = width

  fun freshState () =
    CommandState
    { env = Env.empty
    , tyenv = TyEnv.empty
    , interactive = true
    , width = 80
    , eof = false
    , malt  = false
    }


  (* Warning: O(length(ls)^2) *)
  fun nub eq [] = []
    | nub eq (x::xs) = x :: (nub eq (List.filter (fn a => not (eq (a,x))) xs))

  fun forall action [] = ()
    | forall action (x::xs) = (action x; forall action xs)


  fun output ctx str =
    (print str;
    print "\n")

  fun nl ctx = print "\n"

  fun pretty ctx doc =
    WPrettyPrinter.pretty (getWidth ctx) doc

  fun outputPP ctx doc =
    print $ pretty ctx doc


  fun warning ctx msg =
    (output ctx msg; ctx)

  fun warningPP ctx doc =
  let
    val d = PP.nest 2 $ PP.line
            </PP.join/> PP.text "-- Warning: "
            </PP.join/> doc
  in
    warning ctx $ pretty ctx d
  end


  fun discard (s,p) =
  let
    val c = TextIO.StreamIO.canInput (s,1000000)
  in
    case c of
         NONE => (s,p)
       | SOME k => (snd (TextIO.StreamIO.inputN (s, k)),p)
  end

  (* fun seof (s,p) = TextIO.StreamIO.endOfStream s *)

  fun parserFailMsg (Fail m) = m
    | parserFailMsg (Error m) = m

  fun interactiveStatements ctx prompt statement stEnd stream =
  let
    fun interact ctx stream =
      interactiveStatements ctx prompt statement stEnd stream
    val st = statement ctx
    val _  = (print prompt; print " ")
    val (c,s) =
      case parse st stream of
         RIGHT [(ctx,s)] =>
            if stEnd ctx
                then (ctx,s)
                else (interact ctx s)
       | LEFT [(msg,s)] => (
            print "Error: "; print (parserFailMsg msg); print "\n";
            interact ctx (discard s) )
       | _ => Err.undefined ()
  in
    (c,s)
  end;

  fun tr () = chr #";"

  fun ran env =
    List.concat (map (Env.find env) (Env.dom env))


  structure PPAux = PrettyPrinterAux(WPrettyPrinter)
  local open WPrettyPrinter open PPAux in

  fun ppAgentSupport ctx agent = PPNomPsi.ppSupp agent
  fun ppClause _ cl            = PPClause.ppClause cl
  fun ppClauseFormals _ cl     = PPClause.ppClauseFormals cl
  fun ppAlpha _ act            = PPSAct.ppAction act

  fun ppAgent ctx a = PsiPP.ppAgent a

  fun ppAgentC ctx a =
    text "  " </join/> (nest 2 (ppAgent ctx a)) </join/> line


  fun ppAlphaSim ctx alpha =
    text "--|" </join/> (ppAlpha ctx alpha) </join/> text "|-->"

  fun ppWAlphaSim ctx alpha =
    case alpha of
         WSim.Tr.Silent => text "======>"
       | _ => text "==|"
            </join/>
                (ppAlpha ctx (case alpha of
                                   WSim.Tr.Tau        => Sim.Tr.Act.Tau
                                 | WSim.Tr.Input inp  => Sim.Tr.Act.Input inp
                                 | WSim.Tr.Output out => Sim.Tr.Act.Output out
                                 | _ => Err.undefined () ) )
            </join/> text "|==>"

  fun ppPsi ctx psi = PsiPP.a psi

  fun ppCbrackets ctx doc = text "{|" </sp/> doc </sp/> text "|}"

  (* auxilary function to print typed names *)
  fun printNameTy (na,typ') = 
                PsiPP.n na </sp/> text ":" </sp/> PsiPP.typ typ'

  fun printAssr a = (PsiPP.a a)

  fun ppAtomicConstraint ctx (avec, psi, phi) =
    (if null avec
        then empty
        else text "(new" </sp/>
             commaSep (map printNameTy avec) </join/> text ")") </join/>
             (ppCbrackets ctx $
                (if Psi.Inst.Assr.eqData (psi, Psi.Inst.unit)
                    then empty
                    else PsiPP.a psi </sp/> text "|-" </join/> text " ")
                    </join/> PsiPP.c phi)

  fun ppConstraint ctx c =
    sep (text " /\\ ") $ map (ppAtomicConstraint ctx) c

  fun ppParens ctx d = text "(" </join/> d </join/> text ")"

  fun breakableSp ctx (a,b) = a </join/> nest 2 (line </join/> b)

  local open Bisim.C in
  fun ppBisimConstraint ctx True = text "true"
    | ppBisimConstraint ctx False = text "false"
    | ppBisimConstraint ctx (Atomic a) = ppAtomicConstraint ctx a
    | ppBisimConstraint ctx (Conj (c,c')) =
        group (ppParens ctx $
            ppBisimConstraint ctx c </sp/> text "/\\" </breakableSp ctx/>
            ppBisimConstraint ctx c')
    | ppBisimConstraint ctx (Disj (c,c')) =
        group (ppParens ctx $
            ppBisimConstraint ctx c </sp/> text "\\/" </breakableSp ctx/>
            ppBisimConstraint ctx c')
    | ppBisimConstraint ctx (Imp (c,c')) =
        ppParens ctx $
        ppBisimConstraint ctx c </sp/> text "==>" </breakableSp ctx/>
        ppBisimConstraint ctx c'
    | ppBisimConstraint ctx (TermEq (n,m)) =
        ppCbrackets ctx $ PsiPP.t n </sp/> text "=" </sp/> PsiPP.t m
    | ppBisimConstraint ctx (FreshP (a,p)) =
        ppCbrackets ctx $ PsiPP.n a </sp/> text "#" </sp/> ppAgent ctx p
    | ppBisimConstraint ctx (StImp (psi,psi')) =
        ppCbrackets ctx $ PsiPP.a psi </sp/> text "<=" </sp/> PsiPP.a psi'
  end

  fun ppBisimDisjList ctx l =
    text "<" </join/>
        group (
        sep (text "," </join/> line)
        (map (group o ppBisimConstraint ctx) l) )
            </join/>
    text ">"

  fun ppBisimCNFList ctx l =
    text "[" </join/> nest 2 (
    group (
        line </join/>
        sep (text "," </join/> line)
        (map (ppBisimDisjList ctx) l) ) )
            </join/>
    text "]" </join/> line

  fun ppBisim ctx (c,t) =
    text "Relation:" </breakableSp ctx/>
    ((text "{" </nl/>
       (List.foldr (fn ((i, ((p,q), c) ), d) =>
           text (Int.toString i) </join/> text "." </sp/>
           text "((" </join/> ppAgent ctx p </join/> text ", "
                     </join/> ppAgent ctx q </join/> text "), "
                     </nl/> ppBisimConstraint ctx c
                     </join/> text ")," </join/> line </nl/> d)
           empty (Lst.zip (Lst.enum 1 (length t)) t)))
            </join/> text "}" </join/> line ) </nl/>
    (text "Constraint:" </breakableSp ctx/>
    (ppBisimConstraint ctx c))


  fun ppSol ctx sol =
  let
    fun s sigma = text "[" </join/> commaSep (map (fn (n,t) =>
      PsiPP.n n </sp/> text ":=" </sp/> PsiPP.t t) sigma)
      </join/> text "]"
    fun sl (sigma, psi) = text "(" </join/> commaSep [s sigma, PsiPP.a psi]
      </join/> text ")"
  in
    (fn RIGHT sol' => group $ sep (text "," </join/> line) (map sl sol')
      | _ => text "No solution found")
      sol
  end

  fun ppDescr msg doc =
    text msg </join/> (nest 2 (line </join/> doc))

  fun ppTrans ctx ppAlpha (psi,alpha,c,sol,agent) =
    ppPsi ctx psi </sp/> text "|>" </join/>
        nest 2 (line </join/>
            ppAlpha ctx alpha </join/>
                nest 2 ( line </nl/>
                ppDescr "Constraint:" (ppConstraint ctx c) </nl/>
                ppDescr "Solution:" (ppSol ctx sol) </nl/>
                ppDescr "Derivative:" (ppAgent ctx agent)
            ))

  fun ppTransSim ctx ppAlpha number agent =
    (text (Int.toString number)) </join/> text " ---" </join/>
    (nest 2 (line </join/> ppTrans ctx ppAlpha agent))

  fun dumpEnv ctx =
  let
    val e = getEnv ctx
    val clsn = nub Psi.Inst.Term.eqData (Env.dom e)
    fun pp cl =
      PP.nest 2 (PP.line </PP.join/>
      (ppClause ctx cl) </PP.join/> PP.line)
    val () = forall (fn a =>
        (* TODO: print lets *)
        outputPP ctx (sep line $ map pp (Env.find e a))
    ) clsn
    val () = output ctx "\n"
  in
    () (* outputPP ctx $ (sep line (map (ppClause ctx) (ran e))) *)
  end

  fun dumpTyEnv ctx =
  let
    val e = getTyEnv ctx
   
    fun pp tyName =
      PP.nest 2 (PP.line </PP.join/>
      (printNameTy tyName) </PP.join/> PP.line)
   
    fun ppA assr =
      PP.nest 2 (PP.line </PP.join/>
      (printAssr assr) </PP.join/> PP.line)

    
    val () =
        outputPP ctx (sep line $ map pp (rev (TyEnv.getTEnv e)))

    (* TODO: better printout of assertions *)
    val () =  
        outputPP ctx (ppA (TyEnv.getAssr e)) 

    val () = output ctx "\n"
  in
    () (* outputPP ctx $ (sep line (map (ppClause ctx) (ran e))) *)
  end

  fun drop ctx a =
    updateEnv ctx ((flip Env.remove) a)

  (* fun dropTy ctx a =  *)
  (*   updateTyEnv ctx ((flip TyEnv.remove) a) *)

  fun dropTyEnv ctx = 
    resetTyEnv ctx TyEnv.empty


  end (* local open WPrettyPrinter open PPAux *)


  fun outputClause ctx clause =
    outputPP ctx ((PP.nest 2 (PP.line </PP.join/> ppClause ctx clause))
                                      </PP.join/> PP.line)


  fun freeVariablesInClause cl = SI.ClEnv.Cl.support cl

  (* parsing a name-type pair from command-line *)
  fun parseTy () = 
               name >>=
    (fn t' =>  t ":" >> typ >>=
    (fn p  =>  return (t', p)
    ))

  fun parseAss () = 
    assr >>= (fn a => return a) 

  fun clauseArgs () =
                (t "(" >>
                ((parseTy ()) </sepby/> (t ",")) >>=
    (fn xtvec => t ")" >>
                return xtvec)) </choice/> (return [])


  fun parseClause ctx =
                term >>=
    (fn a =>    clauseArgs () >>=
    (fn xvec => t "<=" >>
                agent () >>=
    (fn p =>    return (a,xvec,p) )))


  fun parseLetClauses ctx =
                t "def" >> t "{" >>
                ((parseClause ctx) </sepby/> (t ";")) >>=
    (fn cls =>  (t ";" </choice/> return "") >>
                t "}" >> tr () >>
                return cls )

   

  fun parseType ctx = 
                t "deftype" >> t "{" >>
                ((parseTy ()) </sepby/> (t ";")) >>=
    (fn tcls => (t ";" </choice/> return "") >>
                t "}" >> tr () >>
                return tcls )

  fun parseAssr ctx = 
                t "deftype" >> t "{" >>
                ((parseAss ()) </sepby/> (t ";")) >>=
    (fn acls => (t ";" </choice/> return "") >>
                t "}" >> tr () >>
                return acls )         



  fun clauseId (a,_,_) = a

  fun checkClauseClosed ctx cl =
  let
    val n = Cl.support cl
  in
    case n of
         [] => RIGHT ()
       | _  => LEFT $
        ppClauseFormals ctx cl
            </PPAux.sp/> PP.text "is not closed, the support is"
            </PPAux.sp/> PP.text "{" </PP.join/>
                            PPAux.commaSep (map PsiPP.n n) </PP.join/>
                         PP.text "}"
  end

  fun invocations (Psi.Nil) = []
    | invocations (Psi.Output _) = []
    | invocations (Psi.Input _) = []
    | invocations (Psi.Case cs) = List.concat $ map (invocations o snd) cs
    | invocations (Psi.Restriction (_,_,p)) = invocations p
    | invocations (Psi.Parallel (p,q)) = (invocations p) @ (invocations q)
    | invocations (Psi.Replication p) = invocations p
    | invocations (Psi.Assertion _) = []
    | invocations (Psi.Invocation inv) = [inv]


  fun checkInvocation env (a,mvec) =
  let
    val cl = List.find (fn (a',xvec,p) =>
                (a </Psi.Inst.Term.eqData/> a') andalso
                    (length xvec = length mvec)) (Env.find env a)
  in
    maybe
        (LEFT $
            PP.text "There is no clause defined "
                </PPAux.sp/> PsiPP.t a </PPAux.sp/> PP.text "with arity"
                </PPAux.sp/> PP.text (Int.toString $ length mvec))
        (const (RIGHT ()))
        cl
  end

  fun checkInvocations env (a,xvec,p) =
    lefts $ map (checkInvocation env) (invocations p)

  (*
   * Check if every call is defined in the environment and in the let {..}
   * Warn if some things will be redefined
   * Check if all clauses are closed *)

  fun checkDrop env a =
    case Env.find env a of
         [] => RIGHT ()
       | _  => LEFT $ (PP.text "redefined clause" </PPAux.sp/> (PsiPP.t a))


  fun checkDroped env cls =
    map (checkDrop env)
        (nub (Psi.Inst.Term.eqData) $ map (fn (a,_,_) => a) cls)


  fun ppInvocation (a,mvec) =
    PsiPP.t a </PP.join/> PP.text "<"
              </PP.join/> PPAux.commaSep (map PsiPP.t mvec)
              </PP.join/> PP.text ">"

  fun checkGuarded ctx env (inv as (a,mvec)) =
    case Guarded.guarded env (Psi.Invocation inv) of
         true  => RIGHT ()
       | false => LEFT $
        PP.text "Invocation" </PPAux.sp/> ppInvocation inv
                             </PPAux.sp/> PP.text "is not guarded."

  fun checkGuardedInvocations ctx env (a,xvec,p) =
    lefts $ map (checkGuarded ctx env) (invocations p)

  fun checkClauseArgs _ [] = true
    | checkClauseArgs acc ((n,t)::xs) = 
        let val acc'  = (n::acc)
            val tSupp = Psi.Inst.Type.support t
        in
          rev (Lst.intersection acc' tSupp) = tSupp 
          andalso checkClauseArgs acc' xs 
        end

  fun letClauses ctx cls =
  let
    val env  = getEnv ctx
    (* drop all the read clauses from the environment *)
    val dropedEnv = List.foldr (fn ((a,_,_),e) => Env.remove e a) env cls
    val wellClauses = List.all (fn (_,xtvec,_) => checkClauseArgs [] xtvec) cls 
  in 
    if not (wellClauses) then
      (print("Err: mallformed clause arguments regarding the free names in types!\n"); return ctx)
    else    
      let      
        (* prepare a type environment to type check the new clauses *)
        val tyEnv = List.foldr (fn ((_,xtvec,_),e) => 
                            Psi.Inst.Env.extendl e xtvec) (getTyEnv ctx) cls
        val tmpEnv = List.foldr (fn ((cl as (a,_,_)),e) => Env.extend e a cl)
                     dropedEnv cls
        val flag = ref false
        (* type check the clauses newly inserted in the environment *) 
        val _ = map (fn (cl as (_,_,p)) => 
                   TypeChecker.typeCheck tyEnv tmpEnv p 
                   handle TypeChecker.Type s => (flag := true; print("\n"^s^"\n\n"))) cls
        (* val flag = List.map (typeCheckCls tyEnv tmpEnv) cls  *)
      in
        if not (!flag) then   
          let 
            val inv = List.concat $ map (checkInvocations tmpEnv) cls
            val closed = lefts $ map (checkClauseClosed ctx) cls
            val droped = lefts $ checkDroped env cls
            val guarded = List.concat $ map (checkGuardedInvocations ctx tmpEnv) cls
            fun warnings docs =
               forall (warningPP ctx) docs
               (* (map (PP.join/>PP.line) docs) *)
            val newCtx = updateEnv ctx (const tmpEnv)
            val _ = if length cls > 1 then output newCtx "\ndef {" else ()
            val _ = forall (fn c => (outputClause newCtx c; output ctx ";")) cls
            val _ = if length cls > 1 then output newCtx "};" else output newCtx ";"
            val _ = warnings (droped @ closed @ inv @ guarded)
          in
            return newCtx
          end
        else return ctx
      end
  end
  
  fun clauseC ctx = parseClause ctx >>= letClauses ctx o sngl
  fun letClausesC ctx = parseLetClauses ctx >>= letClauses ctx


  (* updating the type environment *)
  fun typeCl ctx tycls =
  let 
    val env    = getTyEnv ctx
    val env'   = TyEnv.extendl env tycls
    val newCtx = updateTyEnv ctx (const env')
  in 
    return newCtx
  end

  (* updating the type environment using assertions *)
  fun assrCl ctx acls =
  let 
    val env  = getTyEnv ctx
    val env' = List.foldl (fn (a,e) => TyEnv.extendAssr e a) env acls 
    val newCtx = updateTyEnv ctx (const env')
  in 
    return newCtx
  end

  fun typeC ctx = (parseType ctx >>= typeCl ctx)  
     </choice/> (parseAssr ctx >>= assrCl ctx)

  fun typeEnvC ctx = 
                    t "tyenv" >> tr () >>=
    (fn _ =>    (dumpTyEnv ctx; return ctx))

  (* TODO: nicer printout of an environment *)
  fun envC ctx =
                t "env" >> tr () >>=
    (fn _ =>    (dumpEnv ctx; return ctx))

  fun agentSupport ctx =
                t "n" >>
                t "(" >>
                agent () >>=
    (fn a =>    t ")" >> tr () >>
                (outputPP ctx (PP.text "  " </PP.join/>
                              (ppAgentSupport ctx a
                              </PP.join/> PP.line));
                return ctx)
    )


  fun boolResponse ctx =
    (fn t =>    (outputPP ctx (PP.text (if t then "true" else "false")
                               </PP.join/> PP.line);
                return ctx ))

  fun agentGuarded ctx =
                t "guarded" >> t "(" >> agent () >>=
    (fn a =>    t ")" >> tr () >>
                return (Guarded.guarded (getEnv ctx) a) >>=
                boolResponse ctx)


  fun parseAssignment ctx =
                name >>=
    (fn x =>    t ":=" >>
                term >>=
    (fn t =>    return (x,t)
    ))


  fun parseSubst ctx =
                t "[" >> parseAssignment ctx </sepby1/> t "," >>=
    (fn xts =>  t "]" >>
                return xts)

  fun agentSubst' ctx =
                agent () >>=
    (fn a =>    many1 (parseSubst ctx) >>=
    (fn sigmas => tr () >>
                return $ Lst.foldl (flip Psi.subst) a sigmas))

  fun agentSubst ctx =
                agentSubst' ctx >>=
    (fn a =>    (outputPP ctx (ppAgentC ctx a); return ctx))

  fun agentAgent ctx =
                agent () >>=
    (fn a =>    tr () >>=
    (fn _ =>    (outputPP ctx (ppAgentC ctx a); return ctx)))


  fun agentAlphaEq ctx =
                agent () >>=
    (fn a =>    t "=" >>
                agent () >>=
    (fn b =>    tr () >>=
    (fn _ =>    return (Psi.eqData (a,b) ) >>=
                boolResponse ctx)))

  fun opAgent ctx =
                agentSupport ctx
    </choice/>  agentSubst ctx
    </choice/>  agentGuarded ctx
    </choice/>  agentAlphaEq ctx
    </choice/>  agentAgent ctx

  fun agentC ctx =
                (t "agent" </choice/> return "") >> opAgent ctx



  fun inputEnd ctx = ws >> eof ctx >>= return

  fun redundantDelim ctx = ws >> tr () >> return ctx

  fun dropC ctx =
                t "drop" >> term >>=
    (fn n =>    ws >> tr () >>
                return (drop ctx n))


  (* fun dropTyC ctx =  *)
  (*               t "dropty" >> name >>= *)
  (*   (fn n => ws >> tr () >> *)
  (*               return (dropTy ctx n))  *)


  fun dropTyEnvC ctx = 
                t "droptyenv" >>=
    (fn _ => ws >> tr () >>
                return (dropTyEnv ctx))



  fun number () =
                sat (fn c => c <> #"0" andalso Char.isDigit c) >>=
    (fn a =>    many (sat Char.isDigit) >>=
    (fn r =>    maybe
                    (error "Could not parse integer")
                    return
                    (Int.fromString (String.implode (a :: r)))
    ))


  val  enum = Lst.enum

  fun trS () = singleWS

  fun numCommand ctx =
                ws >> number () >>=
    (fn n =>    trS () >> return n)


  fun stepAgentC
        reduce
        ppAlpha
        (wctx as (ctx,(agent::agents))) =
  let
    fun stransAgent (psi,alpha,c,sol,agent) = agent

    val tr = reduce (getEnv ctx) Sim.Psi.Inst.unit agent
    val transitions = fst $
        List.partition (fn (_,_,_,RIGHT _,_) => true | _ => false) $
        map (fn (psi,p,alpha,c,p') =>
            (psi, alpha, c, SCS.solve (getTyEnv ctx) c, p')) tr


    val n        = List.length transitions
    val nTrans   = zip (enum 1 n) transitions
    fun select x = stransAgent $ List.nth (transitions, x - 1)
 

    val _ = output ctx ((Int.toString n) ^ " possible derivative(s)")
    val _ =
      forall
        (fn (n, trans) =>
            (()
            ; outputPP ctx (ppTransSim ctx ppAlpha n trans)
            ; nl ctx;nl ctx
            )
        ) nTrans
  in
    (           numCommand ctx >>=
    (fn x =>    nofail (if x - 1 < n
                    then return (ctx,((select x)::agent::agents))
                    else error "No such agent") ) )
    </choice/>
                (ws >> str "b" >> nofail (trS () >>
                delayed (fn () =>
                (case agents of
                      [] => Parser.error "Already at the top"
                    | _ => return (ctx,agents)))))
    </choice/>

                (  ((ws >> str "q" >> trS ()) </choice/> (ws >> eof ())) >>
                return (setEof ctx,[])
                )

  end
    | stepAgentC _ _ _ =
        Err.error "sstepAgentC called without giving an agent"


  fun sstepAgentC  wctx =
    stepAgentC Sim.reduce ppAlphaSim wctx


  fun wsstepAgentC wctx =
    stepAgentC WSim.reduce ppWAlphaSim wctx


  (* Type checking the agents. 
   * I have used a flag (ref type) to control the 
   * welltypedness of the agents; then based on this flag,
   * the malt value in the context record is set 
   * accordingly. *)
  fun typeCheckStepC a ctx =
    let
       val env   = getTyEnv ctx
       val clEnv = getEnv ctx
       val flag  = ref false
       val _     = TypeChecker.typeCheck env clEnv a
                   handle TypeChecker.Type s => (flag := true; print("\n"^s^"\n\n"))
    in 
      if !flag then return (setMalformedTy ctx)
      else (return (unSetMalformedTy ctx))
    end

  fun symbolicStepC ctx name stepF =
              t name >> agent () >>=
    (fn a =>  ws >> tr () >> typeCheckStepC a ctx >>= 
              (fn ctx' =>   
                         (direct (fn stream => 
                             if (getMalformedTy (ctx')) then (RIGHT [(ctx',stream)])
                             else 
                                let 
                                  val () = output ctx' "Type <num> for selecting derivative, b - for bactracking, q - quit"
                                  val (_,s) = interactiveStatements
                                             (ctx', [a])
                                             (name ^ ">")
                                             stepF
                                             (isEof o fst)
                                             stream
                                in
                                  (RIGHT [(ctx',s)]) 
                                end 
              )))  
    )
  

  fun typeCheckC ctx =
                     t "typecheck" >> agent () >>= 
  (fn a =>  ws >> tr () >>  typeCheckStepC a ctx)



  fun sstepC ctx =
    symbolicStepC ctx "sstep" sstepAgentC


  fun wsstepC ctx =
    symbolicStepC ctx "wsstep" wsstepAgentC


  fun disjToList (Bisim.C.Disj (c,c')) = disjToList c @ disjToList c'
    | disjToList c = [c]

  fun cnfToList (Bisim.C.Conj (c,c')) = cnfToList c @ cnfToList c'
    | cnfToList c = [disjToList c]


  fun checkBisim ctx (p,q) =
  let
    val b = Bisim.bisim (p,q)
    val sb = (Bisim.C.simplify (Tpl.fst b),
              map (fn (pq,c) => (pq, Bisim.C.simplify c)) (Tpl.snd b))
    (*
    val sb = (Bisim.C.cnf (Tpl.fst sb),
              map (fn (pq,c) => (pq, Bisim.C.cnf c)) (Tpl.snd sb))
    val ll = cnfToList (Tpl.fst sb)
    *)
    val res = SBCS.solve (fn s => fn c => 
                outputPP ctx $ PP.line </PP.join/>
                PP.text ("Debug: " ^ s)  </PP.join/> PP.nest 4
                (PP.line </PP.join/> ppBisimConstraint ctx c) </PP.join/> PP.line)
        (Tpl.fst b)
  in
    ( outputPP ctx $ ppBisim ctx sb ;
     (* ; outputPP ctx $ ppBisimCNFList ctx ll *)
      (*outputPP ctx $ PP.text ("Number of /\\ is " ^ (Int.toString $ length ll))
      ; *)
     output ctx "\n\n";
     outputPP ctx $ ppSol ctx res;
     output ctx "\n";
     ()
     )
  end


  fun bisimC ctx =
                agent () >>=
    (fn p =>    t "~" >>
                agent () >>=
    (fn q =>    tr () >>
                (if useBisim
                   then checkBisim ctx (p,q)
                   else output ctx "NOTE: Bisimulation checking is not available."; 
                   return ctx) ))

  fun warrantyC ctx = 
    ((t "warranty" >> tr ()) >>= (fn _ =>
        (output ctx Copyright.warranty ; return ctx)))

  fun copyrightC ctx = 
    ((t "copyright" >> tr ()) >>= (fn _ =>
        (output ctx Copyright.copyright ; return ctx)))


  fun exitC ctx =
    ((t "exit" >> tr () >> return ctx)
    </choice/>
    (ws >> eof ctx)) >>=
    (fn _ => (return (setEof ctx)))



  (* extending the set of commands to support types*)
  fun commands () =
    exitC          ::
    clauseC        ::
    letClausesC    ::
    redundantDelim ::
    envC           ::
    dropC          ::
    
    typeC          ::
    typeEnvC       ::
    (* dropTyC        :: *)
    dropTyEnvC     :: 
    typeCheckC     ::
    (* assrC          :: *)

    inputC         ::
    sstepC         ::
    wsstepC        ::
    agentC         ::
    bisimC         ::
    warrantyC      ::
    copyrightC     ::
    []

  and statement (ctx : command_state) =
    List.foldl choice zero (map (fn c => c ctx) (commands ()))

  and inputFile ctx n =
  let
    val f = TextIO.openIn n
    val s = ParserStreamIO.make f

    fun eof ctx =
      if isEof ctx
        then return (unsetEof ctx)
        else error "-- End of input unexpected"

    fun script ctx =    (eof ctx)
        </choice/>      (statement ctx >>= script)
  in
    parse (script ctx) s
 end

  and inputC ctx =
                t "input" >> PsiB.literal >>=
    (fn n =>    ws >> tr () >>=
    (fn _ =>    case (inputFile ctx n) of
                       RIGHT ((ctx,s)::_) => return ctx
                     | LEFT ((err,s)::_)  => error (parserFailMsg err)
                     | RIGHT _ => Err.undefined ()
                     | LEFT _ => Err.undefined ()
    ))


  fun repl ctx stream =
    interactiveStatements
        ctx
        "psi>"
        statement
        isEof
        stream


  fun captureStdIn () = ParserStreamIO.make TextIO.stdIn

  fun start' () =
  let
    val state = freshState ()
    val stream = captureStdIn ()
  in
    repl state stream
  end

  fun start () =
  let
    val _ = start' ()
  in
    ()
  end

end;

