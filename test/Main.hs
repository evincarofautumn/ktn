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
            "|]\x27E7->\x2192{{|}...\x2026()\
            \_:::[[|]\x2237\\,;\x2983|}\x2984"

        locdItem <$> testTokenize symbols
          `shouldBe`
          [ Right $ ArrayEnd ASCII
          , Right $ ArrayEnd Unicode
          , Right $ Arrow ASCII
          , Right $ Arrow Unicode
          , Right $ BlockBegin
          , Right $ UnboxedBegin ASCII
          , Right $ BlockEnd
          , Right $ Ellipsis ASCII
          , Right $ Ellipsis Unicode
          , Right $ GroupBegin
          , Right $ GroupEnd
          , Right $ Ignore
          , Right $ Lookup ASCII
          , Right $ Layout
          , Right $ ListBegin
          , Right $ ArrayBegin ASCII
          , Right $ ListEnd
          , Right $ Lookup Unicode
          , Right $ Ref
          , Right $ Seq
          , Right $ Term
          , Right $ UnboxedBegin Unicode
          , Right $ UnboxedEnd ASCII
          , Right $ UnboxedEnd Unicode
          ]

testTokenize = tokenize (TextName "test") (Row 1)
