{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Control.Exception (SomeException, evaluate, try)
import Control.Monad.IO.Class (liftIO)
import Kitten
import Text.PrettyPrint.HughesPJClass (Pretty(..))
import qualified Data.Text as Text
import qualified System.Console.Haskeline as Haskeline
import qualified Text.PrettyPrint as PP

main :: IO ()
main = Haskeline.runInputT Haskeline.defaultSettings loop
  where
    loop = do
      line <- Haskeline.getInputLine "> "
      case line of
        Just "//quit" -> nop
        Just entry -> do
          let entry' = Text.pack [if c == '`' then '\n' else c | c <- entry]
          let interactiveName = TextName "interactive"
          tokens :: SomeException + [Locd (Tok 'Unbrack)]
            <- liftIO $ try $ evaluate
            $ tokenize interactiveName (Row 1) entry'
          case tokens of
            Left e -> nop
            Right tokens' -> do
              bracketed :: SomeException + [Locd (BrackErr + Tok 'Brack)]
                <- liftIO $ try $ evaluate
                $ bracket interactiveName tokens'
              case bracketed of
                Left e -> nop
                Right bracketed' -> do
                  let bracketed'' = [tok | Right tok :@ _loc <- bracketed']
                  Haskeline.outputStrLn $ unlines
                    $ (PP.render . pPrint) <$> bracketed''
          loop
        Nothing -> nop

nop :: (Monad m) =>  m ()
nop = pure ()
