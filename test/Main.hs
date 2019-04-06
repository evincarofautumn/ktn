{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Main (main) where

import Data.Text (Text)
import Kitten
import Test.HUnit
import Test.Hspec
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
          `shouldBe` Right <$>
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
          `shouldBe` Right <$>
          [ Word $ Unqual Postfix "abc"
          ]

      it "parses alphanumeric word names" do
        locdItem <$> testTokenize "abc123"
          `shouldBe` Right <$>
          [ Word $ Unqual Postfix "abc123"
          ]

      it "parses word names starting with underscore" do
        locdItem <$> testTokenize "_abc123"
          `shouldBe` Right <$>
          [ Word $ Unqual Postfix "_abc123"
          ]

      it "parses word names with underscores" do
        locdItem <$> testTokenize "one_two_three"
          `shouldBe` Right <$>
          [ Word $ Unqual Postfix "one_two_three"
          ]

      it "parses simple operator names" do
        locdItem <$> testTokenize "+ - * /"
          `shouldBe` Right <$>
          [ Word $ Unqual Infix "+"
          , Word $ Unqual Infix "-"
          , Word $ Unqual Infix "*"
          , Word $ Unqual Infix "/"
          ]

      it "parses operator names overlapping with symbols" do
        locdItem <$> testTokenize "|| .. \\/ /\\ .#. #.# ->* ||]"
          `shouldBe` Right <$>
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
          `shouldBe` Right <$>
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
        `shouldBe` fmap Right <$>
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
        `shouldBe` Right <$>
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
        `shouldBe` Right <$>
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
        `shouldBe` Right <$>
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
        `shouldBe` Right <$>
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
      locdItem <$> testLayout
        "header:\n\
        \\&"
        `shouldBe`
        [ Right $ Word $ Unqual Postfix "header"
        , Left $ BrackErr
          ("" :@ Loc testName (Row 1) (Col 10) (Row 1) (Col 10))
          "empty layout block"
        ]

    it "raises error on empty layout block" do
      locdItem <$> testLayout
        "header1:\n\
        \header2:\n\
        \  contents\n\
        \\&"
        `shouldBe`
        [ Right $ Word $ Unqual Postfix "header1"
        , Left $ BrackErr
          ("" :@ Loc testName (Row 1) (Col 11) (Row 1) (Col 11))
          "empty layout block"
        , Right $ Word $ Unqual Postfix "header2"
        , Right BlockBegin
        , Right $ Word $ Unqual Postfix "contents"
        , Right Term
        , Right BlockEnd
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

pattern Int32 :: Sig 'Parsed
pattern Int32 <- VarSig _ (UnresUnqual (Unqual Postfix "Int32"))

pattern NameSig :: Text -> Sig 'Parsed
pattern NameSig name <- VarSig _ (UnresUnqual (Unqual Postfix name))

testTokenize :: Text -> [Locd (TokErr + Tok 'Unbrack)]
testTokenize = testTokenizeRow (Row 1)

testTokenizeRow :: Row -> Text -> [Locd (TokErr + Tok 'Unbrack)]
testTokenizeRow row = tokenize testName row

testName :: SrcName
testName = TextName "test"

testLayout :: Text -> [Locd (BrackErr + Tok 'Brack)]
testLayout input = bracket testName
  [tok :@ loc | Right tok :@ loc <- testTokenize input]

testParse :: Text -> Frag [] 'Parsed
testParse input = parse testName
  [tok :@ loc | Right tok :@ loc <- testLayout input]
