{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
#if __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE QuantifiedConstraints #-}
#endif
{-# LANGUAGE UndecidableInstances #-}

module Kitten
  ( Brack(..)
  , Col(..)
  , ErrMsg(..)
  , Loc(..)
  , Locd(..)
  , Row(..)
  , Tok(..)
  , TokErr(..)
  , type (+)
  , tokenize
  ) where

import Data.Text (Text)
import Data.Vector (Vector)
import GHC.Types (Type)
import qualified Text.Megaparsec as Megaparsec

-- | Bracketing of a token: whether it may be a layout token. After bracketing,
-- a stream of tokens of type @[Tok 'Brack]@ contains matched brackets instead
-- of layout tokens.
data Brack :: Type where
  Unbrack :: Brack
  Brack :: Brack
  deriving (Show)

-- | An indentation error.
data BrackErr :: Type where
  BrackErr :: !(Locd Text) -> !ErrMsg -> BrackErr
  deriving (Show)

-- | A column in a source location.
newtype Col = Col Int
  deriving (Show)

-- | An error message.
newtype ErrMsg = ErrMsg Text
  deriving (Show)

-- | The lexical fixity of a word: 'Infix' for operators, 'Postfix' otherwise.
data Fixity :: Type where
  Postfix :: Fixity
  Infix :: Fixity
  deriving (Show)

-- | A program fragment, comprising all the top-level program elements and terms
-- parsed from a source fragment.
data Frag (container :: Type -> Type) (phase :: Phase) :: Type where
  Frag ::
    { fragInsts :: !(f (InstDef p))
    , fragMetas :: !(f (MetaDef p))
    , fragPermSyns :: !(f (PermSyn p))
    , fragPerms :: !(f (PermDef p))
    , fragTerms :: !(f (Term p))
    , fragTraitSyns :: !(f (TraitSyn p))
    , fragTraits :: !(f (TraitDef p))
    , fragTypeSyns :: !(f (TypeSyn p))
    , fragTypes :: !(f (TypeDef p))
    , fragVocabSyns :: !(f (VocabSyn p))
    , fragWordSyns :: !(f (WordSyn p))
    , fragWords :: !(f (WordDef p))
    } -> Frag f p

-- TODO: Use QuantifiedConstraints once Intero supports GHC 8.6.1
deriving instance
#if __GLASGOW_HASKELL__ >= 806
  (forall a. Show (f a))
#else
  ( Show (f (InstDef p))
  , Show (f (MetaDef p))
  , Show (f (PermSyn p))
  , Show (f (PermDef p))
  , Show (f (Term p))
  , Show (f (TraitSyn p))
  , Show (f (TraitDef p))
  , Show (f (TypeSyn p))
  , Show (f (TypeDef p))
  , Show (f (VocabSyn p))
  , Show (f (WordSyn p))
  , Show (f (WordDef p))
  )
#endif
  => Show (Frag f p)

-- | The de Bruijn index of a local variable.
newtype Ind = Ind Int
  deriving (Show)

-- | An instance definition.
data InstDef :: Phase -> Type where
  InstDef ::
    { instName :: !(Name p)
    , instSig :: !(Sig p)
    , instBody :: !(Maybe (Term p))
    } -> InstDef p

deriving instance (Show (Name p)) => Show (InstDef p)

-- | The kind of a type variable.
data Kind :: Phase -> Type where
  StackKind :: Kind p
  ValueKind :: Kind p
  LabelKind :: Kind p
  PermKind :: Kind p
  FunKind :: !(Kind p) -> !(Kind p) -> Kind p
  TypeKind :: !(Name p) -> Kind p

deriving instance (Show (Name p)) => Show (Kind p)

-- | A source location, spanning between two (row, column) pairs in the same
-- source.
data Loc :: Type where
  Loc ::
    { locBeginRow :: !Row
    , locBeginCol :: !Col
    , locEndRow :: !Row
    , locEndCol :: !Col
    } -> Loc
  deriving (Show)

-- | A local variable name after name resolution.
data Local :: Type where
  Local :: Unqual -> Ind -> Local
  deriving (Show)

-- | A value decorated with a source location.
data Locd :: Type -> Type where
  (:@) :: a -> !Loc -> Locd a
  deriving (Show)

-- | A definition of metadata.
data MetaDef :: Phase -> Type where
  MetaDef :: MetaDef p
  deriving (Show)

-- | The type of names in the given compiler phase.
type family Name (phase :: Phase) :: Type where
  Name 'Parsed = Unres
  Name 'Renamed = Res
  Name 'Typechecked = Res
  Name 'Desugared = Res

-- | The definition of a permission.
data PermDef :: Phase -> Type where
  PermDef :: PermDef p
  deriving (Show)

-- | The definition of a permission synonym.
data PermSyn :: Phase -> Type where
  PermSyn :: PermSyn p
  deriving (Show)

-- | The compiler phase, which determines the representation of 'Term's.
data Phase :: Type where
  Parsed :: Phase
  Renamed :: Phase
  Typechecked :: Phase
  Desugared :: Phase
  Specialized :: Phase
  deriving (Show)

-- | A qualified name with the given vocab root.
data Qual :: Root -> Type where
  Qual :: !(Vocab r) -> !Unqual -> Qual r
  deriving (Show)

-- | A resolved name.
data Res :: Type where
  ResQual :: Qual 'Abs -> Res
  ResLocal :: Local -> Res
  deriving (Show)

-- | The root of a vocab qualifier.
data Root :: Type where
  Rel :: Root
  Abs :: Root
  deriving (Show)

-- | A row in a source location.
newtype Row = Row Int
  deriving (Show)

-- | A parsed type signature.
data Sig :: Phase -> Type where
  AppSig :: !(Sig p) -> !(Sig p) -> Sig p
  FunSig
    :: !(Vector (Sig p))
    -> !(Vector (Sig p))
    -> !(Vector (Name p))
    -> Sig p
  StackSig
    :: !(Name p)
    -> !(Vector (Sig p))
    -> !(Name p)
    -> !(Vector (Sig p))
    -> !(Vector (Name p))
    -> Sig p
  VarSig :: Name p -> Sig p
  ForallSig
    :: !(Vector (Var p))
    -> Sig p
    -> Sig p
  ExistsSig
    :: !(Vector (Var p))
    -> Sig p
    -> Sig p

deriving instance (Show (Name p)) => Show (Sig p)

-- | An expression term, indexed by the compiler 'Phase'.
data Term :: Phase -> Type where
  Term :: Term p
  deriving (Show)

-- | A token, indexed by a 'Brack'eting that indicates whether it has been
-- 'bracket'ed.
data Tok :: Brack -> Type where
  Tok :: Tok b
  deriving (Show)

-- | A lexical error.
data TokErr :: Type where
  TokErr :: !(Locd Text) -> !ErrMsg -> TokErr
  deriving (Show)

-- | The definition of a trait.
data TraitDef :: Phase -> Type where
  TraitDef :: TraitDef p
  deriving (Show)

-- | The definition of a trait synonym.
data TraitSyn :: Phase -> Type where
  TraitSyn :: TraitSyn p
  deriving (Show)

-- | The definition of a type.
data TypeDef :: Phase -> Type where
  TypeDef :: TypeDef p
  deriving (Show)

-- | The definition of a type synonym.
data TypeSyn :: Phase -> Type where
  TypeSyn :: TypeSyn p
  deriving (Show)

-- | An unqualified name. The 'Fixity' indicates whether it's a word name
-- ('Postfix') or operator name ('Infix'). Note that this doesn't reflect how
-- the word is called, just its lexical type: a 'Call' term has a separate
-- 'Fixity' describing how the name was used.
data Unqual :: Type where
  Unqual :: !Fixity -> !Text -> Unqual
  deriving (Show)

-- | An unresolved name.
data Unres :: Type where
  UnresUnqual :: Unqual -> Unres
  UnresQualRel :: Qual 'Rel -> Unres
  UnresQualAbs :: Qual 'Abs -> Unres
  deriving (Show)

-- | A variable in a quantifier in a type signature.
data Var :: Phase -> Type where
  Var :: !Unqual -> !(Kind p) -> Var p

deriving instance (Show (Name p)) => Show (Var p)

-- | A vocab qualifier.
data Vocab :: Root -> Type where
  VocabAbs :: !(Vector Unqual) -> Vocab 'Abs
  VocabRel :: !(Vector Unqual) -> Vocab 'Rel

deriving instance Show (Vocab r)

data VocabSyn :: Phase -> Type where
  VocabSyn :: VocabSyn p
  deriving (Show)

data WordDef :: Phase -> Type where
  WordDef :: WordDef p
  deriving (Show)

data WordSyn :: Phase -> Type where
  WordSyn :: WordSyn p
  deriving (Show)

type a + b = Either a b
infixl 6 +

-- | Tokenize a source fragment into a stream of tokens interspersed with
-- lexical errors.
tokenize :: Text -> [Locd (TokErr + Tok 'Unbrack)]
tokenize input = error $ "TODO: tokenize " ++ show input

-- | Convert a stream of tokens with layout-sensitive blocks into one that uses
-- explicit brackets.
bracket :: [Locd (Tok 'Unbrack)] -> [Locd (BrackErr + Tok 'Brack)]
bracket tokens = error $ "TODO: bracket " ++ show tokens

-- | Parse a stream of bracketed tokens into a program fragment.
parse :: [Locd (Tok 'Brack)] -> Frag [] 'Parsed
parse tokens = error $ "TODO: parse " ++ show tokens

-- | Replace unresolved names with resolved names throughout a fragment.
rename :: Frag Vector 'Parsed -> Frag Vector 'Renamed
rename frag = error $ "TODO: rename " ++ show frag

-- | Annotate terms with their types.
typecheck :: Frag Vector 'Renamed -> Frag Vector 'Typechecked
typecheck frag = error $ "TODO: typecheck " ++ show frag

-- | Desugars high-level notation into the core language.
desugar :: Frag Vector 'Typechecked -> Frag Vector 'Desugared
desugar frag = error $ "TODO: desugar " ++ show frag

-- | Specialize polymorphic calls to monomorphic calls, generating
-- instantiations of generic words and instances, and collect arity information.
specialize :: Frag Vector 'Desugared -> Frag Vector 'Specialized
specialize frag = error $ "TODO: specialize " ++ show frag

-- lower :: Frag Vector 'Specialized -> IR
-- codegen :: (Platform p) => IR -> Code p
