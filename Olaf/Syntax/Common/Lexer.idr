module Olaf.Syntax.Common.Lexer

import Text.Lexer

import Toolkit.Text.Lexer.Run

%default total


symbols : List String
symbols = ["->", "=>", "=", ":=", "[", "]", ":", "{", "}", ",", "(", ")", "|"
          ]

keywords : List String
keywords = [ "def", "fun", "let", "in", "rec", "main"

           , "this", "that"

           , "match", "as", "with"

           , "if", "then", "else"

           , "empty", "extend"

           , "true", "false"
           , "unit"
           , "apply"

           -- Operations
           , "and", "not", "or", "xor", "lessThan"
           , "add", "sub"
           , "pack", "unpack"
           , "size"
           , "toChar", "toNat", "toString"

           -- Types
           , "Nat", "Bool", "String", "Char", "List", "Pair", "Sum"
           , "Unit"
           ]

public export
data Identifier = MkIdentifier String

export
Eq Identifier where
  (==) (MkIdentifier x) (MkIdentifier y) = x == y

namespace SystemV
  public export
  data Token = ID String
              | Keyword String
              | LineComment String
              | BlockComment String
              | Documentation String

              | LitNat Nat
              | LitStr String
              | LitChr String

              | Symbol String
              | WS String
              | NotRecognised String
              | EndInput

  showToken : Show a => String -> a -> String
  showToken n a = "(" <+> n <+> " " <+> show a <+> ")"

  export
  Show Token where
    show (ID id)             = showToken "ID" id
    show (Keyword str)       = showToken "Keyword" str
    show (LineComment str)   = showToken "LineComment" str
    show (BlockComment str)  = showToken "BlockComment" str
    show (Documentation str) = showToken "Documentation" str

    show (LitNat n) = showToken "Nat" n
    show (LitStr s) = showToken "Str" s
    show (LitChr s) = showToken "Chr" s

    show (Symbol s) = showToken "Symbol" s
    show (WS ws) = "WS"
    show (NotRecognised s) = showToken "Urgh" s
    show EndInput          = "EndInput"

  export
  Eq Token where
    (==) (ID x) (ID y) = x == y

    (==) (LineComment x) (LineComment y) = x == y
    (==) (BlockComment x) (BlockComment y) = x == y
    (==) (Keyword x) (Keyword y) = x == y

    (==) (LitNat x) (LitNat y) = x == y
    (==) (LitStr x) (LitStr y) = x == y
    (==) (LitChr x) (LitChr y) = x == y

    (==) (Symbol x) (Symbol y) = x == y

    (==) (WS x) (WS y) = x == y
    (==) (NotRecognised x) (NotRecognised y) = x == y
    (==) EndInput EndInput = True
    (==) _ _ = False


  identifier : Lexer
  identifier = pred startIdent <+> many (pred validIdent)
    where
      startIdent : Char -> Bool
      startIdent '_' = True
      startIdent x = isAlpha x

      validIdent : Char -> Bool
      validIdent '_' = True
      validIdent x = isAlphaNum x

  charLit : Lexer
  charLit = is '\'' <+> alphaNum <+> is '\''

  stripQuotes : String -> String
  stripQuotes str = substr 1 (length str `minus` 2) str

  export
  tokenMap : TokenMap SystemV.Token
  tokenMap = with List
    [
      (space, WS)
    , (lineComment (exact "--"), LineComment)
    , (blockComment (exact "{-") (exact "-}"), BlockComment)
    , (digits, \x => LitNat (integerToNat $ cast {to=Integer} x))
    , (stringLit, (LitStr . stripQuotes))
    , (Lexer.charLit, (LitChr . stripQuotes))
    ]
    ++
       map (\x => (exact x, Symbol)) symbols
    ++
    [
      (identifier, (\x => if elem x keywords then Keyword x else ID x))
    , (any, NotRecognised)
    ]

keep : WithBounds SystemV.Token -> Bool
keep (MkBounded t _ _)
  = case t of
      BlockComment _ => False
      LineComment  _ => False
      WS           _ => False
      _              => True

namespace Olaf
  export
  lexer : Lexer Token
  lexer = MkLexer SystemV.tokenMap (keep) EndInput

  namespace String
    export
    lex : String -> Either LexError (List (WithBounds Token))
    lex = lexString Olaf.lexer

  namespace File
    export
    lex : String -> IO $ Either LexFail (List (WithBounds Token))
    lex = lexFile Olaf.lexer
