{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Kitten
import Test.HUnit
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

  describe "test suite" $ do

    it "runs" $ do
      assertEqual "2 + 2 = 4" (2 + 2) 4

  describe "tokenization" $ do

    describe "whitespace" $ do

      it "produces empty output for empty input" $ do
        testTokenize "" `shouldBe` []

      it "produces empty output for all-whitespace input" $ do
        testTokenize " \n\f\r\t\v\x3000" `shouldBe` []

      it "ignores single-line comment" $ do
        testTokenize "// single-line comment\n" `shouldBe` []

      it "ignores single-line comment at end of file" $ do
        testTokenize "// single-line comment" `shouldBe` []

      it "ignores multi-line comment" $ do
        testTokenize
          "/*\n\
          \\tmulti-line\n\
          \\tcomment\n\
          \*/\n\
          \\&"
          `shouldBe` []

      it "ignores nested multi-line comment" $ do
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

    describe "symbols" $ do

      it "parses adjacent symbols distinctly" $ do

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
          , Lookup ASCII
          , Layout
          , ListBegin
          , ArrayBegin ASCII
          , ListEnd
          , Lookup Unicode
          , Quote
          , Ref
          , Seq
          , Splice
          , Term
          , UnboxedBegin Unicode
          , UnboxedEnd ASCII
          , UnboxedEnd Unicode
          ]

      it "parses alphabetic word names" $ do
        locdItem <$> testTokenize "abc"
          `shouldBe` Right <$>
          [ Word $ Unqual Postfix "abc"
          ]

      it "parses alphanumeric word names" $ do
        locdItem <$> testTokenize "abc123"
          `shouldBe` Right <$>
          [ Word $ Unqual Postfix "abc123"
          ]

      it "parses word names starting with underscore" $ do
        locdItem <$> testTokenize "_abc123"
          `shouldBe` Right <$>
          [ Word $ Unqual Postfix "_abc123"
          ]

      it "parses word names with underscores" $ do
        locdItem <$> testTokenize "one_two_three"
          `shouldBe` Right <$>
          [ Word $ Unqual Postfix "one_two_three"
          ]

      it "parses simple operator names" $ do
        locdItem <$> testTokenize "+ - * /"
          `shouldBe` Right <$>
          [ Word $ Unqual Infix "+"
          , Word $ Unqual Infix "-"
          , Word $ Unqual Infix "*"
          , Word $ Unqual Infix "/"
          ]

      it "parses operator names overlapping with symbols" $ do
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

      it "parses operators containing angle brackets" $ do
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

  describe "layout" $ do

    it "desugars basic layout" $ do
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

    it "desugars nested layout" $ do
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

    it "desugars layout with folded lines" $ do
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

    it "desugars nested layout with folded lines" $ do
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

    it "raises error on empty layout block at end of input" $ do
      locdItem <$> testLayout
        "header:\n\
        \\&"
        `shouldBe`
        [ Right $ Word $ Unqual Postfix "header"
        , Left $ BrackErr
          (":" :@ Loc testName (Row 1) (Col 7) (Row 1) (Col 8))
          "start of invalid layout block"
        ]

    it "raises error on empty layout block" $ do
      locdItem <$> testLayout
        "header1:\n\
        \header2:\n\
        \  contents\n\
        \\&"
        `shouldBe`
        [ Right $ Word $ Unqual Postfix "header1"
        , Left $ BrackErr
          (":" :@ Loc testName (Row 1) (Col 8) (Row 1) (Col 9))
          "start of invalid layout block"
        , Right $ Word $ Unqual Postfix "header2"
        , Right BlockBegin
        , Right $ Word $ Unqual Postfix "contents"
        , Right Term
        , Right BlockEnd
        ]

  describe "parsing" $ do

    it "parses empty fragment from empty input" $ do
      testParse "" `shouldBe` emptyFrag

testTokenize = tokenize testName (Row 1)

testName = TextName "test"

testLayout input = bracket testName
  [tok :@ loc | Right tok :@ loc <- testTokenize input]

testParse input = parse testName
  [tok :@ loc | Right tok :@ loc <- testLayout input]
