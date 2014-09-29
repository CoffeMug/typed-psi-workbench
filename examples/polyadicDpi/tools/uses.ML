(*
    uses src/missing,
         src/parser
*)
structure Uses =
struct
  structure Parser = Parser(ParserStreamIO)
  open Parser
  open Missing

  (* val home = "/Users/ramunasgutkovas/PsiWorkBench/" *)
  val home = PsiWorkBencHome.home
  fun translateToFileName f = home ^ f ^ ".ML"
  (* fun translateToFileName f = Path.joinBaseExt {base=f, ext="ML"} *)

  fun isWord chr  = Char.isGraph chr andalso (chr <> #",")
  fun isSpace chr = Char.isSpace chr
  fun toStr l     = String.concat (map Char.toString l)
  val ws          = sat isSpace
  fun word ()     = many1 (sat isWord) >>= (fn l => return (toStr l))

  (*
    <uses-clause> ::= `uses' <word> (`,' <word>)*
  *)
  fun useParser () =
                    str "uses" >> nofail (many1 ws >>
                    ((many ws >> word ()) </sepby1/> (many ws >> chr #",")))

  (*
    <uses-pragma> ::= `(*' <uses-clause> `*)'
  *)
  fun usesParser () =
                    many ws >> str "(*" >> many ws >>
                    useParser () >>=
    (fn uses =>     nofail (many ws >> str "*)" >>
                    return uses))


  fun readUsesFromFile f =
  let
    val f  = translateToFileName f
    val fh = TextIO.openIn f
    val fs = ParserStreamIO.make fh
    val files = parse (usesParser ()) fs
    val () = TextIO.closeIn fh
  in
    case files of
         LEFT ((Parser.Error msg,_)::_) => LEFT  msg
       | RIGHT ((fs,_)::_)              => RIGHT fs
       | _                              => RIGHT []
  end

  fun isLeft (LEFT _) = true
    | isLeft _ = false

  fun whileNoError f [] = RIGHT ()
    | whileNoError f (l::lst) =
    case f l of
         LEFT msg => LEFT msg
       | RIGHT _ => whileNoError f lst


  fun load file =
  let
    val loaded = ref []

    fun loadFile file visited =
      if Lst.member file visited then LEFT "circular" else
      if Lst.member file (!loaded) then RIGHT () else
      case readUsesFromFile file of
           LEFT msg => LEFT msg
         | RIGHT files =>
             let
               val visited = file :: visited
             in
               case whileNoError (fn f => loadFile f visited) files of
                    LEFT msg => LEFT msg
                  | RIGHT () => let val () = loaded := (!loaded) @ [file]
                                in RIGHT () end
             end
  in
    case loadFile file [] of
         LEFT msg => LEFT msg
       | RIGHT _ => RIGHT (!loaded)
  end

  fun forall f [] = ()
    | forall f (l::ls) = let val _ = f l in forall f ls end

  fun uses fref =
    case load fref of
         LEFT msg => Err.error msg
       | RIGHT files =>
           forall use (map (fn f => translateToFileName f) files)
                                (* OS.Path.mkRelative {path=translateToFileName f,
                                                    relativeTo=home}) files) *)


  fun prUse file = translateToFileName file
  fun prUses file =
    case load file of
         LEFT msg => Err.error msg
       | RIGHT files =>
           String.concat
             (map (fn filename => "use \"" ^ prUse filename ^ "\";\n") files)


end;

