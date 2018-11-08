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

testTokenize = tokenize (TextName "test") (Row 1)
