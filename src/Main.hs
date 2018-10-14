{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Control.Exception (SomeException, evaluate, try)
import Control.Monad.IO.Class (liftIO)
import Kitten
import qualified Data.Text as Text
import qualified System.Console.Haskeline as Haskeline

main :: IO ()
main = Haskeline.runInputT Haskeline.defaultSettings loop
  where
    loop = do
      line <- Haskeline.getInputLine "> "
      case line of
        Just "//quit" -> nop
        Just entry -> do
          tokens :: SomeException + [Locd (TokErr + Tok 'Unbrack)]
            <- liftIO $ try $ evaluate $ tokenize $ Text.pack entry
          Haskeline.outputStrLn $ show tokens
          loop
        Nothing -> nop

nop :: (Monad m) =>  m ()
nop = pure ()
