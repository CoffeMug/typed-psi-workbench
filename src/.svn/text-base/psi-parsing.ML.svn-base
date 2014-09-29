(* uses src/parser, src/missing, src/psi *)

signature PSI_PARSER =
sig
  structure Psi    : PSI
  structure Parser : PARSER

  val agent : unit -> Psi.psi Parser.parser
  val term  : Psi.Inst.term Parser.parser
  val name  : Psi.Inst.name Parser.parser
  val typ   : Psi.Inst.ty Parser.parser
  val assr  : Psi.Inst.assertion Parser.parser

  val t : string -> string Parser.parser
  val ws : char list Parser.parser
end;

signature PSI_PARSER_REQ =
sig
  structure Psi : PSI
  val parseName : string -> (string, Psi.Inst.name) Either.either
  val parseTerm : string -> (string, Psi.Inst.term) Either.either
  val parseCond : string -> (string, Psi.Inst.condition) Either.either
  val parseAssr : string -> (string, Psi.Inst.assertion) Either.either

  (* extending the parser to parse type *)
  val parseTy   : string -> (string, Psi.Inst.ty) Either.either
  
  val var       : ((Psi.Inst.name * Psi.Inst.ty) -> Psi.Inst.term) option
  (*val var'    : (Psi.Inst.name -> Psi.Inst.term) option*)


end;


functor PsiParserBase(P: PARSER) :
sig
  val identifier    : string P.parser
  val ws            : char list P.parser
  val literal       : string P.parser
  val singleWS      : unit P.parser
  val stok          : string -> unit P.parser
end =
struct
  open P;
  open Missing;


  val sp = sat Char.isSpace

  val space = many $ sat Char.isSpace

  val nl = #"\n"
  val inlineComment =
    str "--" >> until (chr nl) >> chr nl >> return ()

  fun nestedComment () =
  let
    fun any () =    (delayed nestedComment >> delayed any)
      </choice/>    ((try (str "*)")) >> return ())
      </choice/>    (item >> delayed any)
  in
    str "(*" >> delayed any >> str "*)" >> return ()
  end

  fun comment () = inlineComment
    </choice/>  delayed nestedComment


  val emptyWS = [] : char list

  fun ws' () =
               (space >> comment () >> delayed ws' >> space >> return emptyWS)
    </choice/> (space >> return emptyWS)

  val ws = delayed ws'

  val singleWS =
    (sp >> return ()) </choice/> comment ()

  fun isAlphaNumeric c =
    Char.isAlphaNum(c) orelse c = #"_"

  val identifier' =
                ws >> many1 (sat isAlphaNumeric) >>=
    (fn r =>    many (sat (op = /> #"'")) >>=
    (fn x =>    return (r @ x)
    ))

  val identifier = identifier' >>= return o String.implode

  fun escape beg esc escSym ennd =
    let
      fun rest x =
                    (esc >>= (fn e => rest (escSym::x)))
        </choice/>  (ennd >> return x)
        </choice/>  (item >>= rest o ((op ::) /> x))
    in
      ws >> beg >> rest [] >>= return o reverse
    end

  val doubleQuoteLiteral = escape (chr #"\"") (str "\\\"") (#"\"") (chr #"\"")
  val singleQuoteLiteral = escape (chr #"'") (str "\\'") (#"'") (chr #"'")
  val unescapeLiteral    = escape (str "{*") zero #" " (str "*}")

  val literal' =    doubleQuoteLiteral
       </choice/>   singleQuoteLiteral
       </choice/>   unescapeLiteral

  val literal =     (literal' >>= return o String.implode)
       </choice/>   identifier

  fun stok s =
    (ws >> str s >> return ())
    </choice/> (P.error (s ^ " expected"))
end;


functor PsiParser
    (A:
    sig
      structure Parser : PARSER
      structure Req    : PSI_PARSER_REQ
    end) : PSI_PARSER
=
struct
  structure Psi    = A.Req.Psi
  structure Parser = A.Parser
  structure B      = PsiParserBase(Parser)
  open B
local
  open A.Req
  open Parser
  open Psi
  open Missing
in


  fun parseLiteral p = literal >>= Either.either Parser.error return o p
  val name = parseLiteral parseName
  val assr = parseLiteral parseAssr
  val cond = parseLiteral parseCond
  val term = parseLiteral parseTerm

  val typ  = parseLiteral parseTy  (* parsing of type *)

  fun tok p = ws >> p >>= (fn x => ws >> return x)
  val t = tok o str



  fun nill () = t "0" >> return Nil

  and inputSubj () = ws >> term

  
  (* this function is used to parse a (name,type) pair and is used in input and restriction agents parsing *)
  and nameTypePair () = t "(" >> name >>=
    (fn t' =>  t ":" >> typ >>=
    (fn p  =>  t ")" >> return (t', p)
    ))   

  
  (*modified to support types *)
  and inputObjFullTyped () =
                t "(" >> t "\\" >> nameTypePair () </sepby1/> (t ",") >>=
                        (fn xvect => t ")" >> term >>=
                            (fn n => return (xvect,n)))


  (*modified to support types *)  
  and inputObjAbrTyped () =
                
    nameTypePair () >>=
    (fn nt =>    case A.Req.var of
                     NONE => Parser.error
                        ("Abbreviated form of Input is not supported" ^
                         " by the instance!")
                   | SOME v => return ([nt], v nt)
    )

  and inputObjTyped () = inputObjFullTyped () </choice/> inputObjAbrTyped () 


  and input () =
                        inputSubj () >>=
    (fn m =>            inputObjTyped () >>=
    (fn (xvec, n) =>    return (fn p => Input (m, xvec, n, p))
    ))
  

  and output () =
                t "'" >> term >>=
    (fn m =>    t "<" >> term >>=
    (fn n =>    t ">" >>
                return (fn p => Output (m, n, p))))


  and prefix' () = output () </choice/> input ()
  and prefix  () =
                prefix' () >>=
    (fn p =>    ((t "." >>
                (delayed $ restrictedAgent ["parallel"])) </choice/> return Nil)  >>=
                return o p)

  and caseClause () =
                cond >>=
    (fn cond => t ":" >>
                delayed (restrictedAgent []) >>=
    (fn p =>    return (cond, p)
    ))

  and caseAgent () =
                t "case" >>
                caseClause () </sepby1/> (t "[]") >>=
    (fn cs =>   return (Case cs)
    )
 
  (*modified to support types *)

  and restriction () =
                t "(" >> t "new" >> nameTypePair () </sepby1/> (t ",") >>=
    (fn ns =>   t ")" >>
                delayed (restrictedAgent ["parallel"]) >>=
    (fn a =>    return (ListPair.foldr Restriction a (ListPair.unzip ns))
    ))

  and replication () =
                t "!" >> delayed (restrictedAgent ["replication", "parallel"]) >>=
                return o Replication

  and par () =  (delayed $ restrictedAgent ["parallel"])
    </rightAssocOp1/> (t "|" >> return Parallel)

  and assertion () =
                t "(|" >>
                assr >>=
    (fn psi =>  t "|)" >>
                return (Assertion psi)
    )

  and parens () =
                t "(" >>
                delayed agent >>=
    (fn a =>    t ")" >>
                return a
    )

  and invocation () =
                term >>=
    (fn a =>    t "<" >>
                (term </sepby/> (t ",")) >>=
    (fn mvec => t ">" >>
                return (Invocation (a, mvec))
    ))

  (* From the lowest to the highest priority *)
  and agentProds () =
  ("parallel"    , par            ()) ::
  ("restriction" , restriction    ()) ::
  ("replication" , replication    ()) ::
  ("parens"      , parens         ()) ::
  ("prefix"      , prefix         ()) ::
  ("case"        , caseAgent      ()) ::
  ("invocation"  , invocation     ()) ::
  ("assertion"   , assertion      ()) ::
  ("nil"         , nill           ()) ::
  []

  and restrictedAgent l () =
    List.foldr choice zero $
        map snd $
            (filter (not o (flip member) l o fst) $ agentProds ())

  and agent () = restrictedAgent [] ()

end
end;

