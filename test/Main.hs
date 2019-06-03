{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Main (main) where

import Data.Text (Text)
import Kitten
import Test.HUnit
import Test.Hspec
import qualified Data.Map as M
import qualified Data.Vector as V

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

  describe "tokenization" do

    describe "whitespace" do

      it "produces empty output for empty input" do
        testTokenize "" `shouldBe` []

      it "produces empty output for all-whitespace input" do
        testTokenize " \n\f\r\t\v\x3000" `shouldBe` []

      it "ignores single-line comment" do
        testTokenize "// single-line comment\n" `shouldBe` []

      it "ignores single-line comment at end of file" do
        testTokenize "// single-line comment" `shouldBe` []

      it "ignores multi-line comment" do
        testTokenize
          "/*\n\
          \\tmulti-line\n\
          \\tcomment\n\
          \*/\n\
          \\&"
          `shouldBe` []

      it "ignores nested multi-line comment" do
        testTokenize
          "/*\n\
          \\tnested\n\
          \\t/*\n\
          \\t\tmulti-line\n\
          \\t\tcomment\n\
          \\t*/\n\
          \*/\n\
          \\&"
          `shouldBe` []

    describe "symbols" do

      it "parses adjacent symbols distinctly" do

        -- TODO: < > | \ - _ . \x2192 :
        let
          symbols =
            -- Hmm...   (._. )
            "|]\x27E7-> \x2192{{|}...\x2026()_\
            \:::[[|]\x2237''\\,#;\x2983|}\x2984"

        locdItem <$> testTokenize symbols
          `shouldBe`
          [ ArrayEnd ASCII
          , ArrayEnd Unicode
          , Arrow ASCII
          , Arrow Unicode
          , BlockBegin
          , UnboxedBegin ASCII
          , BlockEnd
          , Ellipsis ASCII
          , Ellipsis Unicode
          , GroupBegin
          , GroupEnd
          , Ignore
          , Look ASCII
          , Layout
          , ListBegin
          , ArrayBegin ASCII
          , ListEnd
          , Look Unicode
          , Quote
          , Ref
          , Seq
          , Splice
          , Term
          , UnboxedBegin Unicode
          , UnboxedEnd ASCII
          , UnboxedEnd Unicode
          ]

      it "parses alphabetic word names" do
        locdItem <$> testTokenize "abc"
          `shouldBe`
          [ Word $ Unqual Postfix "abc"
          ]

      it "parses alphanumeric word names" do
        locdItem <$> testTokenize "abc123"
          `shouldBe`
          [ Word $ Unqual Postfix "abc123"
          ]

      it "parses word names starting with underscore" do
        locdItem <$> testTokenize "_abc123"
          `shouldBe`
          [ Word $ Unqual Postfix "_abc123"
          ]

      it "parses word names with underscores" do
        locdItem <$> testTokenize "one_two_three"
          `shouldBe`
          [ Word $ Unqual Postfix "one_two_three"
          ]

      it "parses simple operator names" do
        locdItem <$> testTokenize "+ - * /"
          `shouldBe`
          [ Word $ Unqual Infix "+"
          , Word $ Unqual Infix "-"
          , Word $ Unqual Infix "*"
          , Word $ Unqual Infix "/"
          ]

      it "parses operator names overlapping with symbols" do
        locdItem <$> testTokenize "|| .. \\/ /\\ .#. #.# ->* ||]"
          `shouldBe`
          [ Word $ Unqual Infix "||"
          , Word $ Unqual Infix ".."
          , Word $ Unqual Infix "\\/"
          , Word $ Unqual Infix "/\\"
          , Word $ Unqual Infix ".#."
          , Word $ Unqual Infix "#.#"
          , Word $ Unqual Infix "->*"
          , Word $ Unqual Infix "||"
          , ListEnd
          ]

      it "parses operators containing angle brackets" do
        locdItem <$> testTokenize "< > << >> <= >= <=>"
          `shouldBe`
          [ Word $ Unqual Infix "<"
          , Word $ Unqual Infix ">"
          , AngleBegin ASCII
          , Word $ Unqual Infix "<"
          , AngleEnd ASCII
          , Word $ Unqual Infix ">"
          , AngleBegin ASCII
          , Word $ Unqual Infix "="
          , AngleEnd ASCII
          , Word $ Unqual Infix "="
          , AngleBegin ASCII
          , Word $ Unqual Infix "=>"
          ]

  describe "source locations" do

    it "offsets tokens by initial source line" do
      testTokenizeRow (Row 10)
        "foo bar\n\
        \baz\n\
        \quux\n\
        \\&"
        `shouldBe`
        [ Word (Unqual Postfix "foo") :@ Loc testName (Row 10) (Col 1) (Row 10) (Col 4)
        , Word (Unqual Postfix "bar") :@ Loc testName (Row 10) (Col 5) (Row 10) (Col 8)
        , Word (Unqual Postfix "baz") :@ Loc testName (Row 11) (Col 1) (Row 11) (Col 4)
        , Word (Unqual Postfix "quux") :@ Loc testName (Row 12) (Col 1) (Row 12) (Col 5)
        ]

  describe "layout" do

    it "desugars basic layout" do
      locdItem <$> testLayout
        "header:\n\
        \  contents\n\
        \\&"
        `shouldBe`
        [ Word $ Unqual Postfix "header"
        , BlockBegin
        , Word $ Unqual Postfix "contents"
        , Term
        , BlockEnd
        ]

    it "desugars nested layout" do
      locdItem <$> testLayout
        "outer:\n\
        \  inner1:\n\
        \    contents\n\
        \  inner2:\n\
        \    contents\n\
        \\&"
        `shouldBe`
        [ Word $ Unqual Postfix "outer"
        , BlockBegin
        , Word $ Unqual Postfix "inner1"
        , BlockBegin
        , Word $ Unqual Postfix "contents"
        , Term
        , BlockEnd
        , Term
        , Word $ Unqual Postfix "inner2"
        , BlockBegin
        , Word $ Unqual Postfix "contents"
        , Term
        , BlockEnd
        , Term
        , BlockEnd
        ]

    it "desugars layout with folded lines" do
      locdItem <$> testLayout
        "header:\n\
        \  line1 line1 line1\n\
        \  line2 line2\n\
        \    line2 line2 line2\n\
        \  line3 line3\n\
        \    line3\n\
        \    line3\n\
        \    line3\n\
        \\&"
        `shouldBe`
        [ Word (Unqual Postfix "header")
        , BlockBegin
        , Word (Unqual Postfix "line1")
        , Word (Unqual Postfix "line1")
        , Word (Unqual Postfix "line1")
        , Term
        , Word (Unqual Postfix "line2")
        , Word (Unqual Postfix "line2")
        , Word (Unqual Postfix "line2")
        , Word (Unqual Postfix "line2")
        , Word (Unqual Postfix "line2")
        , Term
        , Word (Unqual Postfix "line3")
        , Word (Unqual Postfix "line3")
        , Word (Unqual Postfix "line3")
        , Word (Unqual Postfix "line3")
        , Word (Unqual Postfix "line3")
        , Term
        , BlockEnd
        ]

    it "desugars nested layout with folded lines" do
      locdItem <$> testLayout
        "outer:\n\
        \  inner1:\n\
        \    line1 line1\n\
        \      line1\n\
        \    line2\n\
        \      line2\n\
        \      line2\n\
        \  inner2:\n\
        \    line3 line3\n\
        \    line4\n\
        \      line4\n\
        \\&"
        `shouldBe`
        [ Word $ Unqual Postfix "outer"
        , BlockBegin
        , Word $ Unqual Postfix "inner1"
        , BlockBegin
        , Word $ Unqual Postfix "line1"
        , Word $ Unqual Postfix "line1"
        , Word $ Unqual Postfix "line1"
        , Term
        , Word $ Unqual Postfix "line2"
        , Word $ Unqual Postfix "line2"
        , Word $ Unqual Postfix "line2"
        , Term
        , BlockEnd
        , Term
        , Word $ Unqual Postfix "inner2"
        , BlockBegin
        , Word $ Unqual Postfix "line3"
        , Word $ Unqual Postfix "line3"
        , Term
        , Word $ Unqual Postfix "line4"
        , Word $ Unqual Postfix "line4"
        , Term
        , BlockEnd
        , Term
        , BlockEnd
        ]

    it "raises error on empty layout block at end of input" do
      testLayout
        "header:\n\
        \\&"
        `shouldBe`
        [ Word (Unqual Postfix "header")
          :@ Loc testName (Row 1) (Col 1) (Row 1) (Col 7)
        , BrackErr "" "empty layout block"
          :@ Loc testName (Row 1) (Col 10) (Row 1) (Col 10)
        ]

    it "raises error on empty layout block" do
      testLayout
        "header1:\n\
        \header2:\n\
        \  contents\n\
        \\&"
        `shouldBe`
        [ Word (Unqual Postfix "header1")
          :@ Loc testName (Row 1) (Col 1) (Row 1) (Col 8)
        , BrackErr "" "empty layout block"
          :@ Loc testName (Row 1) (Col 11) (Row 1) (Col 11)
        , Word (Unqual Postfix "header2")
          :@ Loc testName (Row 2) (Col 1) (Row 2) (Col 8)
        , BlockBegin
          :@ Loc testName (Row 2) (Col 8) (Row 2) (Col 9)
        , Word (Unqual Postfix "contents")
          :@ Loc testName (Row 3) (Col 3) (Row 3) (Col 11)
        , Term
          :@ Loc testName (Row 3) (Col 11) (Row 3) (Col 11)
        , BlockEnd
          :@ Loc testName (Row 3) (Col 11) (Row 3) (Col 11)
        ]

  describe "parsing" do

    it "parses empty fragment from empty input" do
      testParse "" `shouldBe` emptyFrag

    it "parses single empty absolute vocab" do
      testParse
        "vocab absolute;\n\
        \\&"
        `shouldBe` emptyFrag

    it "parses single empty relative vocab" do
      testParse
        "vocab relative { }\n\
        \\&"
        `shouldBe` emptyFrag

    it "parses empty vocab tree" do
      testParse
        "vocab a;\n\
        \vocab b {\n\
        \  vocab c {}\n\
        \}\n\
        \vocab d::e {\n\
        \}\n\
        \vocab f::g;\n\
        \\&"
        `shouldBe` emptyFrag

    it "parses basic word definition" do
      case testParse "define nop (->) {}" of
        Frag
          { fragWords = [WordDef
            { wordDefName = UnresUnqual (Unqual Postfix "nop")
            , wordDefSig = FunSig _ (V.null -> True) (V.null -> True) (V.null -> True)
            , wordDefBody = Identity () _
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses word definition with 1 input, 1 output" do
      case testParse "define id_int32 (Int32 -> Int32) {}" of
        Frag
          { fragWords = [WordDef
            { wordDefName = UnresUnqual (Unqual Postfix "id_int32")
            , wordDefSig = FunSig _
              (V.toList -> [Int32])
              (V.toList -> [Int32])
              (V.null -> True)
            , wordDefBody = Identity () _
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses word definition with multiple inputs, multiple outputs" do
      case testParse
        "define id_3_int32 (Int32, Int32, Int32 -> Int32, Int32, Int32) {}" of
        Frag
          { fragWords = [WordDef
            { wordDefName = UnresUnqual (Unqual Postfix "id_3_int32")
            , wordDefSig = FunSig _
              (V.toList -> [Int32, Int32, Int32])
              (V.toList -> [Int32, Int32, Int32])
              (V.null -> True)
            , wordDefBody = Identity () _
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses word definition with simple quantifier" do
      case testParse
        "define map_list<A, B> (List<A>, (A -> B) -> List<B>) {}" of
        Frag
          { fragWords = [WordDef
            { wordDefName = UnresUnqual (Unqual Postfix "map_list")
            , wordDefSig = QuantSig _
              (Forall _ (V.toList ->
                [ Var (Unqual Postfix "A") ValueKind
                , Var (Unqual Postfix "B") ValueKind
                ]))
              (FunSig _
                (V.toList ->
                  [ AppSig _ (NameSig "List") (NameSig "A")
                  , (FunSig _
                    (V.toList -> [NameSig "A"])
                    (V.toList -> [NameSig "B"])
                    (V.null -> True))
                  ])
                (V.toList -> [AppSig _ (NameSig "List") (NameSig "B")])
                (V.null -> True))
            , wordDefBody = Identity () _
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses word definition with complex quantifier" do
      case testParse
        "define dimap<F<_, _>, A, B, C as type, D as type, +P>\
        \ (F<A, B>, (C -> A +P), (B -> D +P) -> F<C, D> +P) {}" of
        Frag
          { fragWords = [WordDef
            { wordDefName = UnresUnqual (Unqual Postfix "dimap")
            , wordDefSig = QuantSig _
              (Forall _ (V.toList ->
                [ Var (Unqual Postfix "F")
                  (FunKind ValueKind (FunKind ValueKind ValueKind))
                , Var (Unqual Postfix "A") ValueKind
                , Var (Unqual Postfix "B") ValueKind
                , Var (Unqual Postfix "C") ValueKind
                , Var (Unqual Postfix "D") ValueKind
                , Var (Unqual Postfix "P") PermKind
                ]))
              (FunSig _
                (V.toList ->
                  [ AppSig _
                    (AppSig _ (NameSig "F") (NameSig "A"))
                    (NameSig "B")
                  , (FunSig _
                    (V.toList -> [NameSig "C"])
                    (V.toList -> [NameSig "A"])
                    (V.toList -> [Grant (UnresUnqual (Unqual Postfix "P"))]))
                  , (FunSig _
                    (V.toList -> [NameSig "B"])
                    (V.toList -> [NameSig "D"])
                    (V.toList -> [Grant (UnresUnqual (Unqual Postfix "P"))]))
                  ])
                (V.toList ->
                  [ AppSig _
                    (AppSig _ (NameSig "F") (NameSig "C"))
                    (NameSig "D")
                  ])
                (V.toList -> [Grant (UnresUnqual (Unqual Postfix "P"))]))
            , wordDefBody = Identity () _
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses instance definition without body" do
      case testParse
        "instance neg (Int32 -> Int32);" of
        Frag
          { fragInsts = [InstDef
            { instDefName = UnresUnqual (Unqual Postfix "neg")
            , instDefSig = FunSig _
              (V.toList -> [NameSig "Int32"])
              (V.toList -> [NameSig "Int32"])
              (V.toList -> [])
            , instDefBody = Nothing
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses generic instance definition without body" do
      case testParse
        "instance map<A, B>\
        \ (List<A>, (A -> B) -> List<B>);" of
        Frag
          { fragInsts = [InstDef
            { instDefName = UnresUnqual (Unqual Postfix "map")
            , instDefSig = QuantSig _
              (Forall _ (V.toList ->
                [ Var (Unqual Postfix "A") ValueKind
                , Var (Unqual Postfix "B") ValueKind
                ]))
              (FunSig _
                (V.toList ->
                  [ AppSig _ (NameSig "List") (NameSig "A")
                  , (FunSig _
                    (V.toList -> [NameSig "A"])
                    (V.toList -> [NameSig "B"])
                    (V.toList -> []))
                  ])
                (V.toList ->
                  [ AppSig _ (NameSig "List") (NameSig "B")
                  ])
                (V.toList -> []))
            , instDefBody = Nothing
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses instance definition with body" do
      case testParse
        "instance copy (Int32 -> Int32) {}" of
        Frag
          { fragInsts = [InstDef
            { instDefName = UnresUnqual (Unqual Postfix "copy")
            , instDefSig = FunSig _
              (V.toList -> [NameSig "Int32"])
              (V.toList -> [NameSig "Int32"])
              (V.toList -> [])
            , instDefBody = Just (Identity () _)
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses trait definition without body" do
      case testParse
        "trait neg<T> (T -> T);" of
        Frag
          { fragTraits = [TraitDef
            { traitDefName = UnresUnqual (Unqual Postfix "neg")
            , traitDefSig = QuantSig _
              (Forall _ (V.toList ->
                [ Var (Unqual Postfix "T") ValueKind
                ]))
              (FunSig _
                (V.toList -> [NameSig "T"])
                (V.toList -> [NameSig "T"])
                (V.toList -> []))
            , traitDefBody = Nothing
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses permission definition without body" do
      case testParse
        "permission IO;" of
        Frag
          { fragPerms = [PermDef
            { permDefName = UnresUnqual (Unqual Postfix "IO")
            , permDefBody = Nothing
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, no body" do
      case testParse
        "type Void;" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Void")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList -> []
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, no ctors" do
      case testParse
        "type Void {}" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Void")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList -> []
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, one ctor, no fields, no terminator" do
      case testParse
        "type Unit { case unit }" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Unit")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "unit") Nothing Nothing
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, one ctor, no fields" do
      case testParse
        "type Unit { case unit; }" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Unit")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "unit") Nothing Nothing
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, one ctor, zero anonymous fields, no terminator" do
      case testParse
        "type Unit { case unit () }" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Unit")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "unit") Nothing
                (Just (AnonFields _ (V.toList -> [])))
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, one ctor, zero anonymous fields" do
      case testParse
        "type Unit { case unit (); }" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Unit")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "unit") Nothing
                (Just (AnonFields _ (V.toList -> [])))
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, one ctor, zero named fields" do
      case testParse
        "type Unit { case unit {} }" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Unit")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "unit") Nothing
                (Just (NamedFields _ (V.toList -> [])))
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, one ctor, anonymous field" do
      case testParse
        "type Size { case size (UInt64) }" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Size")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "size") Nothing
                (Just (AnonFields _ (V.toList -> [NameSig "UInt64"])))
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, one ctor, anonymous field, trailing comma" do
      case testParse
        "type Size { case size (UInt64,) }" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Size")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "size") Nothing
                (Just (AnonFields _ (V.toList -> [NameSig "UInt64"])))
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, one ctor, anonymous fields" do
      case testParse
        "type Point { case point (Int32, Int32) }" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Point")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "point") Nothing
                (Just (AnonFields _ (V.toList ->
                  [NameSig "Int32", NameSig "Int32"])))
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, one ctor, named fields, basic types" do
      case testParse
        "type Point { case point { x as Float64; y as Float64; z as Float64 } }" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Point")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "point") Nothing
                (Just (NamedFields _ (V.toList ->
                  [ (Unqual Postfix "x", NameSig "Float64")
                  , (Unqual Postfix "y", NameSig "Float64")
                  , (Unqual Postfix "z", NameSig "Float64")
                  ])))
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, one ctor, named fields, basic types, layout" do
      case testParse
        "type Point:\n\
        \  case point:\n\
        \    x as Float64\n\
        \    y as Float64\n\
        \    z as Float64\n\
        \\&" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Point")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "point") Nothing
                (Just (NamedFields _ (V.toList ->
                  [ (Unqual Postfix "x", NameSig "Float64")
                  , (Unqual Postfix "y", NameSig "Float64")
                  , (Unqual Postfix "z", NameSig "Float64")
                  ])))
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, multiple ctors, no fields" do
      case testParse
        "type Bool { case false; case true }" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Bool")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "false") Nothing Nothing
              , CaseDef _ (Unqual Postfix "true") Nothing Nothing
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, multiple ctors, no fields" do
      case testParse
        "type Bool { case false; case true; }" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Bool")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "false") Nothing Nothing
              , CaseDef _ (Unqual Postfix "true") Nothing Nothing
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, multiple ctors, no fields, layout" do
      case testParse
        "type Bool:\n\
        \  case false\n\
        \  case true\n\
        \\&" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Bool")
            , typeDefQuant = Nothing
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "false") Nothing Nothing
              , CaseDef _ (Unqual Postfix "true") Nothing Nothing
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses type def, generic quantifier" do
      case testParse
        "type Pair<A, B> { case pair (A, B) }" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Pair")
            , typeDefQuant = Just (Forall _ (V.toList ->
              [ Var (Unqual Postfix "A") ValueKind
              , Var (Unqual Postfix "B") ValueKind
              ]))
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "pair") Nothing
                (Just (AnonFields _ (V.toList -> [NameSig "A", NameSig "B"])))
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses complicated type def" do
      case testParse
        "type Example<A, B, +P>:\n\
        \  case ctor1:\n\
        \    field1 as Type1; field2 as (Input -> Output)\n\
        \    field3 as\n\
        \      <T> Type3<T>\n\
        \    field4 as [T] (Type4)\n\
        \  case ctor2 { field1 as (Type1); field2 as Type2 }\n\
        \  case ctor3 <T>\n\
        \    (Type1,)\n\
        \  case ctor4 [T] (Type1, Type2); case ctor5 (); case ctor6\n\
        \\&" of
        Frag
          { fragTypes = [TypeDef
            { typeDefName = UnresUnqual (Unqual Postfix "Example")
            , typeDefQuant = Just (Forall _ (V.toList ->
              [ Var (Unqual Postfix "A") ValueKind
              , Var (Unqual Postfix "B") ValueKind
              , Var (Unqual Postfix "P") PermKind
              ]))
            , typeDefCases = V.toList ->
              [ CaseDef _ (Unqual Postfix "ctor1") Nothing
                (Just (NamedFields _ (V.toList ->
                  [ (Unqual Postfix "field1", NameSig "Type1")
                  , (Unqual Postfix "field2", FunSig _
                    (V.toList -> [NameSig "Input"])
                    (V.toList -> [NameSig "Output"])
                    (V.toList -> []))
                  , ( Unqual Postfix "field3"
                    , QuantSig _
                      (Forall _ (V.toList ->
                        [Var (Unqual Postfix "T") ValueKind]))
                      (AppSig _ (NameSig "Type3") (NameSig "T"))
                    )
                  , ( Unqual Postfix "field4"
                    , QuantSig _
                      (Exists _ (V.toList ->
                        [Var (Unqual Postfix "T") ValueKind]))
                      (NameSig "Type4")
                    )
                  ])))
              , CaseDef _ (Unqual Postfix "ctor2") Nothing
                (Just (NamedFields _ (V.toList ->
                  [ (Unqual Postfix "field1", NameSig "Type1")
                  , (Unqual Postfix "field2", NameSig "Type2")
                  ])))
              , CaseDef _ (Unqual Postfix "ctor3")
                (Just (Forall _ (V.toList ->
                  [Var (Unqual Postfix "T") ValueKind])))
                (Just (AnonFields _ (V.toList -> [NameSig "Type1"])))
              , CaseDef _ (Unqual Postfix "ctor4")
                (Just (Exists _ (V.toList ->
                  [Var (Unqual Postfix "T") ValueKind])))
                (Just (AnonFields _ (V.toList ->
                  [NameSig "Type1", NameSig "Type2"])))
              , CaseDef _ (Unqual Postfix "ctor5") Nothing
                (Just (AnonFields _ (V.toList -> [])))
              , CaseDef _ (Unqual Postfix "ctor6") Nothing Nothing
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses empty metadata about word" do
      case testParse
        "about test {}\n\
        \\&" of
        Frag
          { fragMetas = [MetaDef
            { metaDefTag = WordTag
            , metaDefName = UnresUnqual (Unqual Postfix "test")
            , metaDefQuant = Nothing
            , metaDefData = M.toList -> []
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses empty metadata about type" do
      case testParse
        "about type Int32 {}\n\
        \\&" of
        Frag
          { fragMetas = [MetaDef
            { metaDefTag = TypeTag
            , metaDefName = UnresUnqual (Unqual Postfix "Int32")
            , metaDefQuant = Nothing
            , metaDefData = M.toList -> []
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses metadata about type with quantifier" do
      case testParse
        "about type Optional<T>:\n\
        \  kitten::tests {}\n\
        \\&" of
        Frag
          { fragMetas = [MetaDef
            { metaDefTag = TypeTag
            , metaDefName = UnresUnqual (Unqual Postfix "Optional")
            , metaDefQuant = Just (Forall _
              (V.toList -> [Var (Unqual Postfix "T") ValueKind]))
            , metaDefData = M.toList -> [(Qual
              (VocabAbs (V.toList -> [Unqual Postfix "kitten"]))
              (Unqual Postfix "tests"), Identity{})]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses metadata about permission with various keys" do
      case testParse
        "about permission P:\n\
        \  a::b {}\n\
        \  _::c::d {}\n\
        \  e {}\n\
        \\&" of
        Frag
          { fragMetas = [MetaDef
            { metaDefTag = PermTag
            , metaDefName = UnresUnqual (Unqual Postfix "P")
            , metaDefQuant = Nothing
            , metaDefData = M.toList ->
              [ ( Qual
                  (VocabAbs (V.toList -> [Unqual Postfix "a"]))
                  (Unqual Postfix "b")
                , Identity{}
                )
              , ( Qual
                  (VocabAbs (V.toList -> [Unqual Postfix "c"]))
                  (Unqual Postfix "d")
                , Identity{}
                )
              , ( Qual
                  (VocabAbs (V.toList -> []))
                  (Unqual Postfix "e")
                , Identity{}
                )
              ]
            }]
          } -> pure ()
        other -> assertFailure $ show other

    it "parses metadata about vocab" do
      case testParse
        "about vocab kitten:\n\
        \  kitten::docs {}\n\
        \\&" of
        Frag
          { fragMetas = [MetaDef
            { metaDefTag = VocabTag
            , metaDefName = UnresUnqual (Unqual Postfix "kitten")
            , metaDefQuant = Nothing
            , metaDefData = M.toList -> [(Qual
              (VocabAbs (V.toList -> [Unqual Postfix "kitten"]))
              (Unqual Postfix "docs"), Identity{})]
            }]
          } -> pure ()
        other -> assertFailure $ show other

pattern Int32 :: Sig 'Parsed
pattern Int32 <- VarSig _ (UnresUnqual (Unqual Postfix "Int32"))

pattern NameSig :: Text -> Sig 'Parsed
pattern NameSig name <- VarSig _ (UnresUnqual (Unqual Postfix name))

testTokenize :: Text -> [Locd (Tok 'Unbrack)]
testTokenize = testTokenizeRow (Row 1)

testTokenizeRow :: Row -> Text -> [Locd (Tok 'Unbrack)]
testTokenizeRow row = tokenize testName row

testName :: SrcName
testName = TextName "test"

testLayout :: Text -> [Locd (Tok 'Brack)]
testLayout = bracket testName . testTokenize

testParse :: Text -> Frag [] 'Parsed
testParse = parse testName . testLayout
