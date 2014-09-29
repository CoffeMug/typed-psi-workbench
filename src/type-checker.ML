(* The Type-checker is implemented by a functor.   
 * This functor takes a structure of type FRAME and 
 * one of type PSI_CLAUSE_ENVIRONMENT and returns a 
 * structure of type TYPE_CHECKER. *) 

signature TYPE_CHECKER =     
sig 

  structure Frm   : FRAME
  structure ClEnv : PSI_CLAUSE_ENVIRONMENT

  exception Type of string

  val typeCheck   : Frm.Psi.Inst.Env.env -> ClEnv.env -> Frm.Psi.psi -> unit

end;

functor TypeChecker (A: sig
  structure Fr          : FRAME 
  structure ClEnv       : PSI_CLAUSE_ENVIRONMENT
  sharing ClEnv.Cl.Psi = Fr.Psi
  sharing ClEnv.Cl.Psi.Inst = Fr.Psi.Inst
end) : TYPE_CHECKER =
struct 
 
  local open A
  in
    structure Frm = Fr
    structure ClEnv = ClEnv
  end

  exception Type of string
  (* exception FreshNess of string *)
  
  open Frm
  open ClEnv 
  open Missing

  (* aliases *)
  val checkTerm      = Psi.Inst.checkT 
  val checkCompatIn  = Psi.Inst.compatIn
  val checkCompatOut = Psi.Inst.compatOut
  val checkC         = Psi.Inst.checkC
  val checkAsser     = Psi.Inst.checkA
  val checkPattern   = Psi.Inst.checkAbs

  val supportTy      = Psi.Inst.Type.support
  val swapTy         = Psi.Inst.Type.swap
  val swapAtom       = Psi.Inst.Term.swapAtom  
  val assrSupp       = Psi.Inst.Assr.support
  val termSupp       = Psi.Inst.Term.support
    
  val dom            = Psi.Inst.Env.getMap
  val extendList     = Psi.Inst.Env.extendl
  val extend         = Psi.Inst.Env.extend
  val extendA        = Psi.Inst.Env.extendAssr
 
  val tyEq           = Psi.Inst.Type.eqData 

  exception TypeErr  = Psi.Inst.TypeErr

  structure PAlpha = NominalAlphaTyped(Psi)
  structure FAlpha = NominalAlpha(Frm)
  structure CAlpha = NominalAlpha(Cl)

  structure L = NominalList(Psi.Inst.Type)

  (* TODO: find a better way to do this *)
  fun swap [] l = l
    | swap (ab::pi) l = 
        let val l' = swap_tvec ab l
        in 
          swap pi l'
        end
  and swap_tvec _ [] = []
    | swap_tvec ab ((a,t)::rest) = 
        (swapAtom ab a, swapTy ab t)
         ::(swap_tvec ab rest)


  (* The typeCheck function implements the typing rules *)
  fun typeCheck env clEnv exp =
        case exp of
          Psi.Output (m,n,p)        => checkOutput (m,n,p,env,clEnv)
        | Psi.Input (m,xvec,n,p)    => checkInput (m,xvec,n,p,env,clEnv)  
        | Psi.Case clist            => checkCase clist  env clEnv  
        | Psi.Restriction (n,t,p)   => checkRestriction (n,t,p,env,clEnv)
        | Psi.Parallel (p,p')       => checkParallel (p,p',env,clEnv)   
        | Psi.Replication p         => checkReplication (p,env,clEnv)
        | Psi.Assertion a           => checkAssertion a env clEnv 
        | Psi.Invocation (a,ml)     => checkInvocation (a,ml,env,clEnv)  
        | Psi.Nil                   => ()

  and checkOutput (m,n,p,env,clEnv) = 
    let 
      val Ts = checkTerm env m
               handle TypeErr s => raise Type s    
      val To = checkTerm env n
               handle TypeErr s => raise Type s 
    in
      if (checkCompatOut env Ts To) then typeCheck env clEnv p  
      else raise Type ("Err: Output type compatibility error!")
    end
         
  and checkInput (m,xvec,n,p,env,clEnv) = 
    let
      val supAndBndP = Lst.intersection (Psi.support p) (Lst.fsl xvec @ termSupp m @ termSupp n) 
      val supT  = List.concat (map (fn t => supportTy t) (Lst.scl xvec))
      val domE  = dom env
      val _     = if ((Lst.intersection domE supT) <> supT) then 
                   raise Type ("Err: Free name of T not in E!")
                 else ()
      (* val sXvec = Lst.intersection domE (Lst.fsl xvec)  *)
      val pi    = PAlpha.freshNames domE supAndBndP
      (* val pi'   = PAlpha.freshNames domE sXvec *)
      (* val p     = PAlpha.permute pi p *)
      (* val xvec  = swap pi  xvec *)
      val xvec' = swap pi xvec 
      val env'  = extendList env xvec'
      val Us    = checkTerm env m 
                  handle TypeErr s => raise Type s 
      val Uo    = checkPattern env' xvec' n
                  handle TypeErr s => raise Type s 
    in
      if (checkCompatIn env Us Uo) then typeCheck env' clEnv p
      else raise Type ("Err: Input type compatibility error!")
    end

  and checkRestriction (n,t,p,env,clEnv) =
    let
      (* val supAndBndP = Lst.intersection (Psi.support p) [n]   *)
      val supT = supportTy t
      val domE = dom env 
      val _    = if ((Lst.intersection domE supT) <> supT) then
                   raise Type ("Err: Free name of T not in E!")
                 else ()
      (* val pi   = PAlpha.freshNames domE supAndBndP *)
      (* val p    = PAlpha.permute pi p *)
      (* val xvec = swap pi [(n,t)] *)
      val env' = extendList env [(n,t)] 
    in
      typeCheck env' clEnv p 
    end

  and checkReplication (p,env,clEnv) = typeCheck env clEnv p

  and checkCase [] env clEnv  = ()
    | checkCase ((c,p)::rest) env clEnv = 
    let 
      val Tc = checkC env c
               handle TypeErr s => raise Type s 
      val Tp = typeCheck env clEnv p
    in 
      checkCase rest env clEnv
    end

  and checkAssertion a env clEnv = 
      checkAsser env a handle TypeErr s => raise Type s
  
  (* To implement this rule, we need the frame of each agent 
   * freshness conditions: 
   * 1-dom(E1) # dom(E)
   * 2-dom(E2) # dom(E)
   * We collect the assertions and bindings occured in the other agents
   * while type-check the opposite process and vice versa. *)                        
  and checkParallel (p,q,env,clEnv) = 
    let 
      val domE      = dom env

      (* dom(Ep1) # dom(E) *)
      val fQ        = Frm.f q
      val bindersFQ = Frm.binders fQ
      val fQNames   = (Lst.fsl bindersFQ) 
      val ffQ       = FAlpha.makeFresh fQNames fQ domE       
      val env'      = extendList env (Frm.binders ffQ)
      val env''     = extendA env' (Frm.assertion ffQ)
      val _         = typeCheck env'' clEnv p 

      (* dom(Ep1) # dom(E) *)
      val fP        = Frm.f p
      val bindersFP = Frm.binders fP
      val fPNames   = (Lst.fsl bindersFP) 
      val ffP       = FAlpha.makeFresh fPNames fP domE       
      val env'      = extendList env (Frm.binders ffP)
      val env''     = extendA env' (Frm.assertion ffP)
      val _         = typeCheck env'' clEnv q 
    in  
      ()
    end

  (* 
   *                        n(P) subsetequal xvec 
   *                     |xvec| = |Mvec|  guarded(P)
   *                       (A,xvec,Tvec,P) in e  
   *                    Psi,e |> P[xvec := Mvec] -> P'
   *  Invocation ---------------------------------------------
   *                        Psi,e |> A<Mvec> -> P' 
   *
   *  **********************************************************
   *
   *        e |- well-formed , E,e |- Mvec:((xvec,yvec).Tvec) 
   *                      (A,xvec,Tvec,P) in e   
   *  Inv ---------------------------------------------------- yvec # E, Mvec, xvec
   *                       E,e |- A<Mvec> 
   *)

  and checkInvocation (a,ml,env,clEnv) = 
    let 
      val clauses = ClEnv.find clEnv a
      val valid   = List.filter 
         (fn (cl as (a,xtvec,p)) =>
             (List.length xtvec = List.length ml)) clauses           
    in 
      case valid of
        [] =>  print ("Err: The clause is not defined in the clause environment! \n")
      | _  =>  
        let
          val mtvec = map (fn m => checkTerm env m handle TypeErr s => raise Type s) ml
          val tyvec = List.concat $ map supportTy mtvec
          val _     = map (fn (cl as (a,xtvec,_)) => 
                             CAlpha.makeFresh (Lst.fsl xtvec) cl tyvec) valid
          val _     = map (fn (a,xtvec,_) =>
                             let val tvec = Lst.scl xtvec
                             in 
                               if not (Lst.all tyEq (Lst.zip tvec mtvec)) then
                               raise Type ("Err: Type error in identifier arguments!")
                               else ()
                             end) valid                             
        in 
          ()
        end  
    end

end;


