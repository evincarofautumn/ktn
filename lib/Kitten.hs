{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Kitten
  ( CaseDef(..)
  , CaseFields(..)
  , Col(..)
  , Enc(..)
  , ErrMsg(..)
  , Fixity(..)
  , Frag(..)
  , Indented(..)
  , InstDef(..)
  , Kind(..)
  , Loc(..)
  , Locd(..)
  , PermDef(..)
  , Permit(..)
  , Phase(..)
  , Quant(..)
  , Row(..)
  , Sig(..)
  , SrcName(..)
  , Term(..)
  , Tok(..)
  , TokPhase(..)
  , TraitDef(..)
  , TypeDef(..)
  , Unqual(..)
  , Unres(..)
  , Var(..)
  , WordDef(..)
  , type (+)
  , bracket
  , colVal
  , emptyFrag
  , locdItem
  , locdLoc
  , parse
  , rowVal
  , tokenize
  ) where

import Control.Applicative (Alternative(..), empty, many, optional, some)
import Control.Arrow ((|||))
import Control.Monad (guard, join, mzero, void)
import Data.Char
import Data.Foldable (asum, toList)
import Data.Function (on)
import Data.List (foldl', groupBy)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Ord (Down(..), comparing)
import Data.Proxy (Proxy(..))
import Data.Ratio ((%))
import Data.Semigroup (sconcat)
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Void (Void)
import GHC.Exts (IsString)
import GHC.Types (Type)
import Lens.Micro ((^.), Lens')
import Text.PrettyPrint.HughesPJClass (Pretty(..))
import Text.Read (Read(..), readMaybe)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Vector as V
import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MC
import qualified Text.Megaparsec.Char.Lexer as ML
import qualified Text.Megaparsec.Error as ME
import qualified Text.ParserCombinators.ReadPrec as RP
import qualified Text.PrettyPrint as PP
import qualified Text.Read as TR

-- | The type of annotations in the given compiler phase.
type family Anno (phase :: Phase) :: Type where
  Anno 'Parsed = ()
  Anno 'Renamed = ()
  Anno 'Typechecked = Ty
  Anno 'Desugared = Ty

-- | The radix of an numeric literal.
data Base :: Type where
  Bin :: Base
  Oct :: Base
  Dec :: Base
  Hex :: Base
  deriving (Eq, Ord, Show)

-- | The boxity of a term that may be unboxed or boxed.
data Box :: Type where
  Unbox :: Box
  Box :: Box
  deriving (Eq, Show)

-- | Phase of a token: whether it may be a layout token. After bracketing, a
-- stream of tokens of type @[Tok 'Brack]@ contains matched brackets instead of
-- layout tokens.
data TokPhase :: Type where
  Unbrack :: TokPhase
  Brack :: TokPhase
  deriving (Show)

-- | A bracket inserter.
type Bracketer = MP.Parsec Void [Indented (Locd (Tok 'Unbrack))]

-- | The definition of a constructor of a type.
data CaseDef :: Phase -> Type where
  CaseDef ::
    { caseDefLoc :: !Loc
    , caseDefName :: !Unqual
    , caseDefQuant :: !(Maybe (Quant p))
    , caseDefFields :: !(Maybe (CaseFields p))
    } -> CaseDef p

deriving instance (Eq (Anno p), Eq (Name p)) => Eq (CaseDef p)
deriving instance (Show (Anno p), Show (Name p)) => Show (CaseDef p)

-- | The fields of a constructor.
--
-- TODO: Include flag for trailing comma?
data CaseFields :: Phase -> Type where
  AnonFields :: !Loc -> !(Vector (Sig p)) -> CaseFields p
  NamedFields :: !Loc -> !(Vector (Unqual, Sig p)) -> CaseFields p

deriving instance (Eq (Anno p), Eq (Name p)) => Eq (CaseFields p)
deriving instance (Show (Anno p), Show (Name p)) => Show (CaseFields p)

-- | The contents of a character literal.
data CharLit :: Type where
  CharLit :: !(Esc + Char) -> CharLit
  deriving (Eq, Ord, Show)

-- | A column in a source location.
newtype Col = Col Int
  deriving (Enum, Eq, Ord, Read, Show)

colVal :: Col -> Int
colVal (Col val) = val

-- | A trait constraint.
data Constraint :: Phase -> Type where
  Constraint :: !(Name p) -> !(Vector (Sig p)) -> Constraint p

deriving instance (Eq (Name p)) => Eq (Constraint p)
deriving instance (Show (Name p)) => Show (Constraint p)

-- | A top-level program element.
data Elem :: Phase -> Type where
  InstElem :: InstDef p -> Elem p
  MetaElem :: MetaDef p -> Elem p
  PermSynElem :: PermSyn p -> Elem p
  PermElem :: PermDef p -> Elem p
  TermElem :: Term p -> Elem p
  TraitSynElem :: TraitSyn p -> Elem p
  TraitElem :: TraitDef p -> Elem p
  TypeSynElem :: TypeSyn p -> Elem p
  TypeElem :: TypeDef p -> Elem p
  VocabSynElem :: VocabSyn p -> Elem p
  WordSynElem :: WordSyn p -> Elem p
  WordElem :: WordDef p -> Elem p

-- | The encoding of a token with both ASCII and Unicode spellings.
data Enc :: Type where
  ASCII :: Enc
  Unicode :: Enc
  deriving (Eq, Ord, Show)

-- | An error message.
newtype ErrMsg = ErrMsg Text
  deriving (Eq, IsString, Ord, Show)

-- | An escape in a character, text, or paragraph literal.
data Esc :: Type where

  -- ASCII Control Codes

  -- | @\\0@, @\\NUL@: U+0000 NULL
  NUL :: Esc
  -- | @\\SOH@: U+0001 START OF HEADING
  SOH :: Esc
  -- | @\\STX@: U+0002 START OF TEXT
  STX :: Esc
  -- | @\\ETX@: U+0003 END OF TEXT
  ETX :: Esc
  -- | @\\EOT@: U+0004 END OF TRANSMISSION
  EOT :: Esc
  -- | @\\ENQ@: U+0005 ENQUIRE
  ENQ :: Esc
  -- | @\\ACK@: U+0006 ACKNOWLEDGE
  ACK :: Esc
  -- | @\\a@, @\\BEL@: U+0007 BELL
  BEL :: Esc
  -- | @\\b@, @\\BS@: U+0008 BACKSPACE
  BS :: Esc
  -- | @\\t@, @\\HT@, @\\TAB@: U+0009 HORIZONTAL TABULATION
  HT :: Esc
  -- | @\\n@, @\\LF@: U+000A LINE FEED
  LF :: Esc
  -- | @\\v@, @\\VT@: U+000B VERTICAL TABULATION
  VT :: Esc
  -- | @\\f@, @\\FF@: U+000C FORM FEED
  FF :: Esc
  -- | @\\r@, @\\CR@: U+000D CARRIAGE RETURN
  CR :: Esc
  -- | @\\SO@: U+000E SHIFT OUT
  SO :: Esc
  -- | @\\SI@: U+000F SHIFT IN
  SI :: Esc
  -- | @\\DLE@: U+0010 DATA LINK ESCAPE
  DLE :: Esc
  -- | @\\DC1@: U+0011 DEVICE CONTROL 1
  DC1 :: Esc
  -- | @\\DC2@: U+0012 DEVICE CONTROL 2
  DC2 :: Esc
  -- | @\\DC3@: U+0013 DEVICE CONTROL 3
  DC3 :: Esc
  -- | @\\DC4@: U+0014 DEVICE CONTROL 4
  DC4 :: Esc
  -- | @\\NAK@: U+0015 NEGATIVE ACKNOWLEDGE
  NAK :: Esc
  -- | @\\SYN@: U+0016 SYNCHRONOUS IDLE
  SYN :: Esc
  -- | @\\ETB@: U+0017 END OF TRANSMISSION BLOCK
  ETB :: Esc
  -- | @\\CAN@: U+0018 CANCEL
  CAN :: Esc
  -- | @\\EM@: U+0019 END OF MEDIUM
  EM :: Esc
  -- | @\\SUB@: U+001A SUBSTITUTION
  SUB :: Esc
  -- | @\\e@, @\\ESC@: U+001B ESCAPE
  ESC :: Esc
  -- | @\\FS@: U+001C FILE SEPARATOR
  FS :: Esc
  -- | @\\GS@: U+001D GROUP SEPARATOR
  GS :: Esc
  -- | @\\RS@: U+001E RECORD SEPARATOR
  RS :: Esc
  -- | @\\US@: U+001F UNIT SEPARATOR
  US :: Esc
  -- | @\\s@, @\\SP@: U+0020 SPACE
  SP :: Esc
  -- | @\\DEL@: U+007F DELETE
  DEL :: Esc

  -- Other

  -- | @'@: U+0027 APOSTROPHE
  Apos :: Esc
  -- | @\\\\@: U+005C BACKSLASH
  Backslash :: Esc
  -- | @\\N@, @\\bN@, @\\oN@, @\\xN@: Unicode character number in decimal,
  -- binary, octal, or hexadecimal, respectively
  Code :: !Char -> Esc
  -- | @\\cC@, @\\^C@:
  --
  -- * @\\c\@@: U+0000 NULL
  -- * @\\cA@ - @\\cZ@: U+0001 - U+001A
  -- * @\\c[@: U+001B ESCAPE
  -- * @\\c\\@: U+001C FILE SEPARATOR
  -- * @\\c]@: U+001D GROUP SEPARATOR
  -- * @\\c^@: U+001E RECORD SEPARATOR
  -- * @\\c_@: U+001F UNIT SEPARATOR
  Ctrl :: !Char -> Esc
  -- | Empty escape
  Empty :: Esc
  -- | String gap
  Gap :: !Char -> Esc
  -- | @"@: U+0022 QUOTATION MARK
  Quot :: Esc

  deriving (Eq, Ord, Show)

-- | The lexical fixity of a word: 'Infix' for operators, 'Postfix' otherwise.
data Fixity :: Type where
  Postfix :: Fixity
  Infix :: Fixity
  deriving (Eq, Ord, Show)

-- | The precision of a floating-point number.
data FloatBits :: Type where
  F32 :: FloatBits
  F64 :: FloatBits
  deriving (Eq, Ord, Show)

-- | A floating-point literal of the form @FloatLit a b c bits@ denoting the
-- floating-point number @a * 10 ^ (c - b)@ with precision of @bits@.
data FloatLit :: Type where
  FloatLit ::
    { floatLitSig :: !Integer
    , floatLitFrac :: !Int
    , floatLitExp :: !Int
    , floatLitBits :: !FloatBits
    } -> FloatLit
  deriving (Eq, Ord, Show)

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

-- TODO: instance (forall a. Monoid (f a)) => Monoid Frag?
emptyFrag :: (Alternative f) => Frag f p
emptyFrag = Frag
  { fragInsts = empty
  , fragMetas = empty
  , fragPermSyns = empty
  , fragPerms = empty
  , fragTerms = empty
  , fragTraitSyns = empty
  , fragTraits = empty
  , fragTypeSyns = empty
  , fragTypes = empty
  , fragVocabSyns = empty
  , fragWordSyns = empty
  , fragWords = empty
  }


mapFrag :: (forall a. f a -> f a) -> Frag f p -> Frag f p
mapFrag f Frag{..} = Frag
  { fragInsts = f fragInsts
  , fragMetas = f fragMetas
  , fragPermSyns = f fragPermSyns
  , fragPerms = f fragPerms
  , fragTerms = f fragTerms
  , fragTraitSyns = f fragTraitSyns
  , fragTraits = f fragTraits
  , fragTypeSyns = f fragTypeSyns
  , fragTypes = f fragTypes
  , fragVocabSyns = f fragVocabSyns
  , fragWordSyns = f fragWordSyns
  , fragWords = f fragWords
  }

deriving instance
  (Show (Anno p), Show (Name p), forall a. Show a => Show (f a))
  => Show (Frag f p)

deriving instance
  (Eq (Anno p), Eq (Name p), forall a. Eq a => Eq (f a))
  => Eq (Frag f p)

-- | The de Bruijn index of a local variable.
newtype Ind = Ind Int
  deriving (Show)

-- | A value decorated with an indent level.
data Indented :: Type -> Type where
  (:>) ::
    { indentedItem :: a
    , indentedLevel :: !Col
    } -> Indented a
  deriving (Eq, Functor, Ord, Show)

infixl 6 :>

instance (Pretty a) => Pretty (Indented a) where
  pPrint = pPrint . indentedItem

-- | A name instantiated with type arguments.
data Instd :: Phase -> Type where
  Instd :: Name p -> !(Vector (Sig p)) -> Instd p

deriving instance (Eq (Name p)) => Eq (Instd p)
deriving instance (Show (Name p)) => Show (Instd p)

-- | An instance definition.
data InstDef :: Phase -> Type where
  InstDef ::
    { instDefLoc :: !Loc
    , instDefName :: !(Name p)
    , instDefSig :: !(Sig p)
    , instDefBody :: !(Maybe (Term p))
    } -> InstDef p

deriving instance (Eq (Anno p), Eq (Name p)) => Eq (InstDef p)
deriving instance (Show (Anno p), Show (Name p)) => Show (InstDef p)

-- | The precision and range of an integer.
data IntBits :: Type where
  I8 :: IntBits
  I16 :: IntBits
  I32 :: IntBits
  I64 :: IntBits
  U8 :: IntBits
  U16 :: IntBits
  U32 :: IntBits
  U64 :: IntBits
  deriving (Eq, Ord, Show)

-- | An integer literal.
data IntLit :: Type where
  IntLit ::
    { intLitVal :: !Integer
    , intLitBase :: !Base
    , intLitBits :: !IntBits
    } -> IntLit
  deriving (Eq, Ord, Show)

-- | The kind of a type variable.
data Kind :: Phase -> Type where
  StackKind :: Kind p
  ValueKind :: Kind p
  LabelKind :: Kind p
  PermKind :: Kind p
  FunKind :: !(Kind p) -> !(Kind p) -> Kind p
  TypeKind :: !(Name p) -> Kind p

deriving instance (Eq (Name p)) => Eq (Kind p)
deriving instance (Show (Name p)) => Show (Kind p)

-- | A source location, spanning between two (row, column) pairs in the same
-- source.
data Loc :: Type where
  Loc ::
    { locName :: !SrcName
    , locBeginRow :: !Row
    , locBeginCol :: !Col
    , locEndRow :: !Row
    , locEndCol :: !Col
    } -> Loc
  deriving (Eq)

data Loc' :: Type where
  Loc' :: !SrcName -> !Row -> !Col -> !Row -> !Col -> Loc'
  deriving (Read)

-- | Copied from its derived implementation as if it were defined using
-- positional syntax instead of record notation.
instance Show Loc where
  showsPrec p (Loc name beginRow beginCol endRow endCol)
    = showParen (p >= 11)
    $ showString "Loc "
    . showsPrec 11 name
    . showChar ' '
    . showsPrec 11 beginRow
    . showChar ' '
    . showsPrec 11 beginCol
    . showChar ' '
    . showsPrec 11 endRow
    . showChar ' '
    . showsPrec 11 endCol

-- | Copied from its derived implementation as if it were defined using
-- positional syntax instead of record notation.
instance Read Loc where
  readPrec = TR.parens $ RP.prec 10 $ do
    TR.Ident "Loc" <- TR.lexP
    name <- RP.step readPrec
    beginRow <- RP.step readPrec
    beginCol <- RP.step readPrec
    endRow <- RP.step readPrec
    endCol <- RP.step readPrec
    return $ Loc name beginRow beginCol endRow endCol

class HasLoc a where
  location :: Lens' a Loc

-- | The 'Ord' instance for 'Loc' sorts lexicographically by source name, then
-- in /increasing/ order of starting position, and finally in /decreasing/ order
-- of ending position (length).
instance Ord Loc where
  compare a b = mconcat
    [ comparing locName a b
    , comparing locBeginRow a b
    , comparing locBeginCol a b
    , comparing (Down . locEndRow) a b
    , comparing (Down . locEndCol) a b
    ]

instance Semigroup Loc where
  a <> b
    | locName a == locName b = Loc
    { locName = locName a
    , locBeginRow = beginRow
    , locBeginCol = beginCol
    , locEndRow = endRow
    , locEndCol = endCol
    }
    | otherwise = error $ concat
      [ "internal location error: cannot combine locations from different sources "
      , show $ locName a
      , " and "
      , show $ locName b
      ]
    where
      (beginRow, beginCol)
        = (locBeginRow a, locBeginCol a)
        `min` (locBeginRow b, locBeginCol b)
      (endRow, endCol)
        = (locEndRow a, locEndCol a)
        `max` (locEndRow b, locEndCol b)

-- | A local variable name after name resolution.
data Local :: Type where
  Local :: Unqual -> Ind -> Local
  deriving (Show)

-- | A value decorated with a source location.
data Locd :: Type -> Type where
  (:@) :: a -> !Loc -> Locd a
  deriving (Eq, Functor, Ord, Read, Show)

infixl 7 :@

locdItem :: Locd a -> a
locdItem (x :@ _) = x

locdLoc :: Locd a -> Loc
locdLoc (_ :@ loc) = loc

instance (Pretty a) => Pretty (Locd a) where
  pPrint = pPrint . locdItem

-- | A definition of metadata.
data MetaDef :: Phase -> Type where
  MetaDef :: MetaDef p
  deriving (Eq, Show)

-- | The type of names in the given compiler phase.
type family Name (phase :: Phase) :: Type where
  Name 'Parsed = Unres
  Name 'Renamed = Res
  Name 'Typechecked = Res
  Name 'Desugared = Res

-- | The contents of a paragraph literal.
data ParaLit :: Type where
  ParaLit :: !(Vector (Vector (Esc + Text))) -> ParaLit
  deriving (Eq, Ord, Show)

-- | A token parser.
type Parser = MP.Parsec Void [Locd (Tok 'Brack)]

-- | The definition of a permission.
data PermDef :: Phase -> Type where
  PermDef ::
    { permDefLoc :: !Loc
    , permDefName :: !(Name p)
    , permDefBody :: !(Maybe (Term p))
    } -> PermDef p

deriving instance (Eq (Anno p), Eq (Name p)) => Eq (PermDef p)
deriving instance (Show (Anno p), Show (Name p)) => Show (PermDef p)

data Permit :: Phase -> Type where
  Grant :: !(Name p) -> Permit p
  Revoke :: !(Name p) -> Permit p

deriving instance (Eq (Name p)) => Eq (Permit p)
deriving instance (Show (Name p)) => Show (Permit p)

-- | The definition of a permission synonym.
data PermSyn :: Phase -> Type where
  PermSyn ::
    { permSynLoc :: !Loc
    , permSynName :: !(Name p)
    , permSynOf :: !(Vector (Permit p))
    } -> PermSyn p

deriving instance (Eq (Name p)) => Eq (PermSyn p)
deriving instance (Show (Name p)) => Show (PermSyn p)

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
  deriving (Eq, Show)

-- | A universal or existential quantifier.
data Quant :: Phase -> Type where
  Forall :: !Loc -> !(Vector (Var p)) -> Quant p
  Exists :: !Loc -> !(Vector (Var p)) -> Quant p

deriving instance (Eq (Name p)) => Eq (Quant p)
deriving instance (Show (Name p)) => Show (Quant p)

instance HasLoc (Quant p) where
  location :: Lens' (Quant p) Loc
  location f = \ case
    Forall loc vs -> (\ loc' -> Forall loc' vs) <$> f loc
    Exists loc vs -> (\ loc' -> Exists loc' vs) <$> f loc

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
  deriving (Eq, Ord, Read, Show)

rowVal :: Row -> Int
rowVal (Row val) = val

-- | A parsed type signature.
data Sig :: Phase -> Type where
  AppSig :: !Loc -> !(Sig p) -> !(Sig p) -> Sig p
  FunSig
    :: !Loc
    -> !(Vector (Sig p))
    -> !(Vector (Sig p))
    -> !(Vector (Permit p))
    -> Sig p
  StackSig
    :: !Loc
    -> !Unqual
    -> !(Vector (Sig p))
    -> !Unqual
    -> !(Vector (Sig p))
    -> !(Vector (Permit p))
    -> Sig p
  VarSig :: !Loc -> Name p -> Sig p
  QuantSig
    :: !Loc
    -> Quant p
    -> Sig p
    -> Sig p

deriving instance (Eq (Name p)) => Eq (Sig p)
deriving instance (Show (Name p)) => Show (Sig p)

instance HasLoc (Sig p) where
  location f = \ case
    AppSig loc a b -> (\ loc' -> AppSig loc' a b) <$> f loc
    FunSig loc l r p -> (\ loc' -> FunSig loc' l r p) <$> f loc
    StackSig loc l ls r rs p -> (\ loc' -> StackSig loc' l ls r rs p) <$> f loc
    VarSig loc n -> (\ loc' -> VarSig loc' n) <$> f loc
    QuantSig loc q s -> (\ loc' -> QuantSig loc' q s) <$> f loc

-- | The name of a source of code.
data SrcName :: Type where
  FileName :: FilePath -> SrcName
  TextName :: !Text -> SrcName
  deriving (Eq, Ord, Read, Show)

-- | An expression term, indexed by the compiler 'Phase'.
data Term :: Phase -> Type where

  -- A term annotated with a type:
  --
  -- > term as T
  --
  -- Or, when applied as a section, the identity function specialized to a
  -- particular type (and arity) for documenting or debugging the type of the
  -- current program state:
  --
  -- > (as T1, ..., TN)
  -- > // =
  -- > (-> temp1 as T1, ..., tempn as TN; temp1 ... tempn)
  --
  -- It is necessary to differentiate these two because when a term is annotated
  -- with a type, the type needs to be scoped over the whole term in order to
  -- correctly maintain polymorphism.
  --
  -- > "as" <sig>
  -- > "(" "as" <sig> ("," <sig>)* ")"
  As
    :: Anno p
    -> !(Maybe (Term p))
    -> !(Sig p)
    -> Term p

  -- > <term> <term>
  Compose
    :: Anno p
    -> !(Term p)
    -> !(Term p)
    -> Term p

  -- > "call"
  Call
    :: Anno p
    -> Loc
    -> Term p

  -- > "do" "(" <term>* ")" <block>
  Do
    :: Anno p
    -> !(Term p)
    -> !(Term p)
    -> Term p

  Generic
    :: !Loc
    -> !Unqual
    -> !(Term p)
    -> Term p

  -- > "(" <term> ")"
  Group
    :: !Loc
    -> !(Term p)
    -> Term p

  -- >
  Identity
    :: Anno p
    -> !Loc
    -> Term p

  -- > "if" ("(" <term> ")")?
  -- >     <block>
  -- >   ("elif" "(" <term> ")" <block>)*
  -- >   ("else" <block>)?
  If
    :: !Loc
    -> Anno p
    -> !(Maybe (Term p))
    -> !(Vector (Loc, Term p, Term p))
    -> !(Maybe (Loc, Term p))
    -> Term p

  -- If the name is infix but the call is postfix, this is an operator invoked
  -- as a postfix function; if the call is infix, it's a normal infix operator
  -- call. If the name is postfix, the call is always postfix, since there's
  -- currently no notation for using a named word as an infix operator.
  --
  -- > <name>
  -- > "(" <op> ")"
  Invoke
    :: Anno p
    -> !Loc
    -> !Fixity
    -> !(Name p)
    -> Term p

  -- > "jump"
  Jump
    :: Anno p
    -> Loc
    -> Term p

  -- Lexical lifetimes, create new scope:
  -- Lambda
  --   :: !Loc
  --   -> !(Vector (Loc, Maybe Unqual, Maybe (Sig p)))
  --   -> !(Term p)
  --   -> Term p
  --
  -- Non-lexical lifetimes, just introduce variable:
  -- Lambda
  --   :: !Loc
  --   -> !(Vector (Loc, Maybe Unqual, Maybe (Sig p)))
  --   -> Term p

  -- > "[" (<term>* ("," <term>*)*)? ","? "]"
  -- > "[|" (<term>* ("," <term>*)*)? ","? "|]"
  List
    :: Anno p
    -> !Loc
    -> !Box
    -> !(Vector (Term p))
    -> Term p

  -- > "loop"
  Loop
    :: Anno p
    -> Loc
    -> Term p

  -- > "match" ("(" <term> ")")?
  -- >   ("case" <name> <block>)*
  -- >   ("else" <block>)?
  Match
    :: Anno p
    -> !Loc
    -> !(Maybe (Term p))
    -> !(Vector (Loc, Unqual, Term p))
    -> !(Maybe (Loc, Term p))
    -> Term p

  -- A fully applied infix operator call.
  --
  -- > <term>* <name> <term>*
  Operator
    :: Anno p
    -> !Loc
    -> !(Term p)
    -> !(Name p)
    -> !(Term p)
    -> Term p

  -- > "'" (<esc> | <char>) "'"
  -- > U+2018 (<esc> | <char>) U+2019
  PushChar
    :: Anno p
    -> !Loc
    -> !Enc
    -> !CharLit
    -> Term p

  -- > /[-+U+2212]?[0-9]+\.[0-9]+([Ee][-+U+2212]?[0-9]+)?(f[0-9]+)?/
  PushFloat
    :: Anno p
    -> !Loc
    -> !FloatLit
    -> Term p

  -- > /[-+U+2212]?(0(b[01]+|o[0-7]+|x[0-9A-Fa-f]+|[0-9])|[1-9][0-9]*)(i[0-9]+|u[0-9]+)?/
  PushInt
    :: Anno p
    -> !Loc
    -> !IntLit
    -> Term p

  -- > '"""' <lf> (<ws>)* ((\1 (<esc> | <char>)*)? <lf>)* '"""'
  PushPara
    :: Anno p
    -> !Loc
    -> !ParaLit
    -> Term p

  -- > '"' (<esc> | <char>)* '"'
  PushText
    :: Anno p
    -> !Loc
    -> !TextLit
    -> Term p

  -- > "{" (<term>* (";" <term>*))? ";"? "}"
  -- > "{|" (<term>* (";" <term>*))? ";"? "|}"
  Quotation
    :: Anno p
    -> !Loc
    -> !Box
    -> !(Term p)
    -> Term p

  -- > "\\" <term>
  Reference
    :: Anno p
    -> !Loc
    -> !(Term p)
    -> Term p

  -- > "return"
  Return
    :: Anno p
    -> Loc
    -> Term p

  -- > "(" <name> <term>* ")"
  -- > "(" <term>* <name> ")"
  Section
    :: Anno p
    -> !Loc
    -> !(Name p)
    -> !(Term p + Term p)
    -> Term p

deriving instance (Eq (Anno p), Eq (Name p)) => Eq (Term p)
deriving instance (Show (Anno p), Show (Name p)) => Show (Term p)

-- | An existential type variable in a type.
newtype TEVar = TEVar (Var 'Renamed)
  deriving (Show)

-- | The contents of a text literal.
data TextLit :: Type where
  TextLit :: !(Vector (Esc + Text)) -> TextLit
  deriving (Eq, Ord, Show)

-- | A token, indexed by a 'TokPhase' that indicates whether it has been
-- 'bracket'ed and whether it contains lexical errors.
data Tok :: TokPhase -> Type where

  -- Keywords

  -- | @about@ keyword.
  KwdAbout :: Tok b
  -- | @as@ keyword.
  KwdAs :: Tok b
  -- | @case@ keyword.
  KwdCase :: Tok b
  -- | @define@ keyword.
  KwdDefine :: Tok b
  -- | @do@ keyword.
  KwdDo :: Tok b
  -- | @elif@ keyword.
  KwdElif :: Tok b
  -- | @else@ keyword.
  KwdElse :: Tok b
  -- | @export@ keyword.
  KwdExport :: Tok b
  -- | @if@ keyword.
  KwdIf :: Tok b
  -- | @import@ keyword.
  KwdImport :: Tok b
  -- | @instance@ keyword.
  KwdInstance :: Tok b
  -- | @intrinsic@ keyword.
  KwdIntrinsic :: Tok b
  -- | @jump@ keyword.
  KwdJump :: Tok b
  -- | @match@ keyword.
  KwdMatch :: Tok b
  -- | @loop@ keyword.
  KwdLoop :: Tok b
  -- | @permission@ keyword.
  KwdPermission :: Tok b
  -- | @return@ keyword.
  KwdReturn :: Tok b
  -- | @synonym@ keyword.
  KwdSynonym :: Tok b
  -- | @trait@ keyword.
  KwdTrait :: Tok b
  -- | @type@ keyword.
  KwdType :: Tok b
  -- | @vocab@ keyword.
  KwdVocab :: Tok b
  -- | @with@ keyword.
  KwdWith :: Tok b

  -- Symbols

  -- | Left angle bracket: U+003C LESS THAN SIGN or U+27E8 MATHEMATICAL LEFT
  -- ANGLE BRACKET.
  AngleBegin :: !Enc -> Tok b
  -- | Right angle bracket: U+003E GREATER THAN SIGN or U+27E9 MATHEMATICAL
  -- RIGHT ANGLE BRACKET.
  AngleEnd :: !Enc -> Tok b
  -- | Beginning of unboxed array: U+005B LEFT SQUARE BRACKET U+007C VERTICAL
  -- LINE or U+27E6 MATHEMATICAL LEFT WHITE SQUARE BRACKET.
  ArrayBegin :: !Enc -> Tok b
  -- | End of array: U+007C VERTICAL LINE U+005D RIGHT SQUARE BRACKET or U+27E7
  -- MATHEMATICAL RIGHT WHITE SQUARE BRACKET.
  ArrayEnd :: !Enc -> Tok b
  -- | Rightwards arrow: U+002D HYPHEN-MINUS U+003E GREATER THAN SIGN or U+2192
  -- RIGHTWARDS ARROW.
  Arrow :: !Enc -> Tok b
  -- | Beginning of block: U+007B LEFT CURLY BRACKET.
  BlockBegin :: Tok b
  -- | End of block: U+007D RIGHT CURLY BRACKET.
  BlockEnd :: Tok b
  -- | To-do placeholder or stack kind sigil: U+002E U+002E U+002E PERIOD or
  -- U+2026 HORIZONTAL ELLIPSIS.
  Ellipsis :: !Enc -> Tok b
  -- | Beginning of group: U+0028 LEFT PARENTHESIS.
  GroupBegin :: Tok b
  -- | End of group: U+0029 RIGHT PARENTHESIS.
  GroupEnd :: Tok b
  -- | Ignored placeholder, global scope, value kind sigil: U+005F UNDERSCORE.
  Ignore :: Tok b
  -- | Beginning of layout block: U+003A COLON.
  Layout :: Tok b
  -- | Beginning of list: U+005B LEFT SQUARE BRACKET.
  ListBegin :: Tok b
  -- | End of list: U+005D RIGHT SQUARE BRACKET.
  ListEnd :: Tok b
  -- | Vocabulary lookup: U+003A U+003A COLON or U+2237 PROPORTION.
  Look :: !Enc -> Tok b
  -- | Compile-time quotation: @''@.
  Quote :: Tok b
  -- | Reference to term: U+005C BACKSLASH.
  Ref :: Tok b
  -- | Sequence delimiter: U+002C COMMA.
  Seq :: Tok b
  -- | Compile-time splice: U+0023 NUMBER SIGN.
  Splice :: Tok b
  -- | Terminator: U+003B SEMICOLON.
  Term :: Tok b
  -- | Beginning of unboxed closure: U+007B LEFT CURLY BRACKET U+007C VERTICAL
  -- LINE or U+2983 LEFT WHITE CURLY BRACKET.
  UnboxedBegin :: !Enc -> Tok b
  -- | End of unboxed closure: U+007C VERTICAL LINE U+007D RIGHT CURLY BRACKET
  -- or U+2984 RIGHT WHITE CURLY BRACKET.
  UnboxedEnd :: !Enc -> Tok b

  -- Literals

  -- | Character literal.
  Char :: !Enc -> !CharLit -> Tok b
  -- | Floating-point literal.
  Float :: !FloatLit -> Tok b
  -- | Integer literal.
  Integer :: !IntLit -> Tok b
  -- | Paragraph literal.
  Para :: !Enc -> !ParaLit -> Tok b
  -- | Text literal.
  Text :: !Enc -> !TextLit -> Tok b

  -- Identifiers

  -- | Word name.
  Word :: !Unqual -> Tok b

  -- | A lexical error.
  --
  -- TODO: Add a flag to disable this constructor to exclude errors.
  TokErr :: !Text -> !ErrMsg -> Tok b

  -- | An indentation error.
  --
  -- TODO: Add a flag to disable this constructor to exclude errors.
  BrackErr :: !Text -> !ErrMsg -> Tok 'Brack

deriving instance Eq (Tok b)
deriving instance Ord (Tok b)
deriving instance Show (Tok b)

instance Pretty (Tok b) where
  pPrint = \ case
    KwdAbout -> "about"
    KwdAs -> "as"
    KwdCase -> "case"
    KwdDefine -> "define"
    KwdDo -> "do"
    KwdElif -> "elif"
    KwdElse -> "else"
    KwdExport -> "export"
    KwdIf -> "if"
    KwdImport -> "import"
    KwdInstance -> "instance"
    KwdIntrinsic -> "intrinsic"
    KwdJump -> "jump"
    KwdMatch -> "match"
    KwdLoop -> "loop"
    KwdPermission -> "permission"
    KwdReturn -> "return"
    KwdSynonym -> "synonym"
    KwdTrait -> "trait"
    KwdType -> "type"
    KwdVocab -> "vocab"
    KwdWith -> "with"
    AngleBegin ASCII -> "<"
    AngleBegin Unicode -> "\x27E8"
    AngleEnd ASCII -> ">"
    AngleEnd Unicode -> "\x27E9"
    ArrayBegin ASCII -> "[|"
    ArrayBegin Unicode -> "\x27E6"
    ArrayEnd ASCII -> "|]"
    ArrayEnd Unicode -> "\x27E7"
    Arrow ASCII -> "->"
    Arrow Unicode -> "\x2192"
    BlockBegin -> "{"
    BlockEnd -> "}"
    Ellipsis ASCII -> "..."
    Ellipsis Unicode -> "\x2026"
    GroupBegin -> "("
    GroupEnd -> ")"
    Ignore -> "_"
    Layout -> ":"
    ListBegin -> "["
    ListEnd -> "]"
    Look ASCII -> "::"
    Look Unicode -> "\x2237"
    Quote -> "''"
    Ref -> "\\"
    Seq -> ","
    Splice -> "#"
    Term -> ";"
    UnboxedBegin ASCII -> "{|"
    UnboxedBegin Unicode -> "\x2983"
    UnboxedEnd ASCII -> "|}"
    UnboxedEnd Unicode -> "\x2984"
    Char ASCII lit -> PP.hcat ["'", "..." {- pPrint lit -}, "'"]
    Char Unicode lit -> PP.hcat ["\x2018", "..." {- pPrint lit -}, "\x2019"]
    Float lit -> "..." {- pPrint lit -}
    Integer lit -> "..." {- pPrint lit -}
    Para ASCII lit -> PP.vcat ["\"\"\"", "..." {- pPrint lit -}, "\"\"\""]
    Para Unicode lit -> PP.vcat ["\x00B6", "..." {- pPrint lit -}, "\x00B6"]
    Text ASCII lit -> PP.hcat ["\"", "..." {- pPrint lit -}, "\""]
    Text Unicode lit -> PP.hcat ["\x201C", "..." {- pPrint lit -}, "\x201D"]
    Word name -> pPrint name
    TokErr src (ErrMsg msg) -> PP.hcat
      [PP.text $ T.unpack src, " /*", PP.text $ T.unpack msg, "*/"]
    BrackErr src (ErrMsg msg) -> PP.hcat
      [PP.text $ T.unpack src, " /*", PP.text $ T.unpack msg, "*/"]

-- | A character tokenizer.
type Tokenizer = MP.Parsec Void Text

-- | The definition of a trait.
data TraitDef :: Phase -> Type where
  TraitDef ::
    { traitDefLoc :: !Loc
    , traitDefName :: !(Name p)
    , traitDefSig :: !(Sig p)
    , traitDefBody :: !(Maybe (Term p))
    } -> TraitDef p

deriving instance (Eq (Anno p), Eq (Name p)) => Eq (TraitDef p)
deriving instance (Show (Anno p), Show (Name p)) => Show (TraitDef p)

-- | The definition of a trait synonym.
data TraitSyn :: Phase -> Type where
  TraitSyn ::
    { traitSynLoc :: !Loc
    , traitSynName :: !(Name p)
    , traitSynOf :: !(Vector (Constraint p))
    } -> TraitSyn p

deriving instance (Eq (Anno p), Eq (Name p)) => Eq (TraitSyn p)
deriving instance (Show (Anno p), Show (Name p)) => Show (TraitSyn p)

-- | A type variable in a type.
newtype TVar = TVar (Var 'Renamed)
  deriving (Show)

-- | A type in the typechecker.
data Ty :: Type where
  TyApp :: !Loc -> !Ty -> !Ty -> Ty
  TyCon :: !Loc -> !(Qual 'Abs) -> Ty
  TyVar :: !Loc -> !TVar -> Ty
  TyEVar :: !Loc -> !TEVar -> Ty
  TyFun :: !Loc -> !Ty -> !Ty -> Ty
  TyForall :: !Loc -> !TVar -> !Ty -> Ty
  TyExists :: !Loc -> !TVar -> !Ty -> Ty
  deriving (Show)

-- | The definition of a type.
data TypeDef :: Phase -> Type where
  TypeDef ::
    { typeDefLoc :: !Loc
    , typeDefName :: !(Name p)
    , typeDefQuant :: !(Maybe (Quant p))
    , typeDefCases :: !(Vector (CaseDef p))
    } -> TypeDef p

deriving instance (Eq (Anno p), Eq (Name p)) => Eq (TypeDef p)
deriving instance (Show (Anno p), Show (Name p)) => Show (TypeDef p)

-- | The definition of a type synonym.
data TypeSyn :: Phase -> Type where
  TypeSyn ::
    { typeSynLoc :: !Loc
    , typeSynName :: !(Name p)
    , typeSynOf :: !(Sig p)
    } -> TypeSyn p

deriving instance (Eq (Anno p), Eq (Name p)) => Eq (TypeSyn p)
deriving instance (Show (Anno p), Show (Name p)) => Show (TypeSyn p)

-- | An unqualified name. The 'Fixity' indicates whether it's a word name
-- ('Postfix') or operator name ('Infix'). Note that this doesn't reflect how
-- the word is called, just its lexical type: a 'Call' term has a separate
-- 'Fixity' describing how the name was used.
data Unqual :: Type where
  Unqual :: !Fixity -> !Text -> Unqual
  deriving (Eq, Ord, Show)

instance Pretty Unqual where
  pPrint (Unqual _fixity name) = PP.text $ T.unpack name

-- | An unresolved name.
data Unres :: Type where
  UnresUnqual :: Unqual -> Unres
  UnresQualRel :: Qual 'Rel -> Unres
  UnresQualAbs :: Qual 'Abs -> Unres
  deriving (Eq, Show)

-- | A variable in a quantifier in a type signature.
data Var :: Phase -> Type where
  Var :: !Unqual -> !(Kind p) -> Var p

deriving instance (Eq (Name p)) => Eq (Var p)
deriving instance (Show (Name p)) => Show (Var p)

-- | A vocab qualifier.
data Vocab :: Root -> Type where
  VocabAbs :: !(Vector Unqual) -> Vocab 'Abs
  VocabRel :: !(Vector Unqual) -> Vocab 'Rel

deriving instance Eq (Vocab r)
deriving instance Show (Vocab r)

data VocabSyn :: Phase -> Type where
  VocabSyn ::
    { vocabSynLoc :: !Loc
    , vocabSynName :: !(Vocab 'Rel)
    , vocabSynOf :: !(Name p)
    } -> VocabSyn p

deriving instance (Eq (Name p)) => Eq (VocabSyn p)
deriving instance (Show (Name p)) => Show (VocabSyn p)

-- | A tree of vocab definitions containing program elements. This is intended
-- for preserving the organization of definitions for pretty printing.
--
-- A 'VocabLeaf' is a top-level program element. A 'VocabRelBranch' is a
-- vocabulary introduced with block syntax (@vocab foo::bar { ... }@), relative
-- to its parent vocabulary. A 'VocabAbsBranch' is a vocabulary introduced with
-- top-level syntax (@vocab foo::bar; ...@), relative to the global vocabulary.
data VocabTree :: Phase -> Type where
  VocabLeaf :: Elem p -> VocabTree p
  VocabRelBranch :: Vocab 'Rel -> [VocabTree p] -> VocabTree p
  VocabAbsBranch :: Vocab 'Abs -> [VocabTree p] -> VocabTree p

flattenVocabTree :: VocabTree p -> [Elem p]
flattenVocabTree = go (VocabAbs mempty)
  where
    go :: Vocab 'Abs -> VocabTree p -> [Elem p]
    go (VocabAbs parts) = \ case
      -- TODO: add vocab prefix to names
      VocabLeaf e -> pure e
      VocabRelBranch (VocabRel parts') vs
        -> go (VocabAbs (parts <> parts')) =<< vs
      VocabAbsBranch (VocabAbs parts') vs
        -> go (VocabAbs parts') =<< vs

data WordDef :: Phase -> Type where
  WordDef ::
    { wordDefLoc :: !Loc
    , wordDefName :: !(Name p)
    , wordDefSig :: !(Sig p)
    , wordDefBody :: !(Term p)
    } -> WordDef p

deriving instance (Eq (Anno p), Eq (Name p)) => Eq (WordDef p)
deriving instance (Show (Anno p), Show (Name p)) => Show (WordDef p)

data WordSyn :: Phase -> Type where
  WordSyn ::
    { wordSynLoc :: !Loc
    , wordSynName :: !(Name p)
    , wordSynQuant :: !(Maybe (Quant p))
    , wordSynOf :: !(Instd p)
    } -> WordSyn p

deriving instance (Eq (Name p)) => Eq (WordSyn p)
deriving instance (Show (Name p)) => Show (WordSyn p)

type a + b = Either a b
infixl 6 +

-- | Tokenize a source fragment into a stream of tokens interspersed with
-- lexical errors.
tokenize :: SrcName -> Row -> Text -> [Locd (Tok 'Unbrack)]
tokenize srcName row input = case MP.runParser tokenizer name input of
  Left err -> error $ concat
    [ "internal tokenizer error: "
    , MP.errorBundlePretty err
    ]
  Right result -> result
  where
    name :: String
    name = show srcName

    firstLine :: MP.Pos
    firstLine = MP.mkPos $ rowVal row

    tokenizer :: Tokenizer [Locd (Tok 'Unbrack)]
    tokenizer = do
      MP.updateParserState \ s -> s
        { MP.statePosState = (MP.statePosState s)
          { MP.pstateSourcePos = MP.SourcePos name firstLine MP.pos1 } }
      file

    file :: Tokenizer [Locd (Tok 'Unbrack)]
    file = MP.between silence MP.eof tokens

    silence :: Tokenizer ()
    silence = ML.space MC.space1
      (ML.skipLineComment "//")
      (ML.skipBlockCommentNested "/*" "*/")

    locdsym :: Text -> Tokenizer (Locd Text)
    locdsym = ML.lexeme silence . locd . MC.string

    locdsym' :: Text -> Tok b -> Tokenizer (Locd (Tok b))
    locdsym' sym tok = (tok <$) <$> locdsym sym

    locdsymNot :: Tokenizer a -> Text -> Tok b -> Tokenizer (Locd (Tok b))
    locdsymNot exclude sym tok = MP.try $ fmap (fmap (const tok))
      $ ML.lexeme silence $ locd $ MC.string sym
        <* MP.notFollowedBy (MP.try exclude)

    locdkwd :: Text -> Tokenizer (Locd Text)
    locdkwd = ML.lexeme silence . locd
      . (<* MP.notFollowedBy (MP.try wordChar)) . MC.string

    locdkwd' :: Text -> Tok b -> Tokenizer (Locd (Tok b))
    locdkwd' kwd tok = (tok <$) <$> locdkwd kwd

    wordChar :: Tokenizer Char
    wordChar = MP.satisfy isWordChar

    wordStart :: Tokenizer Char
    wordStart = MP.satisfy isWordStart

    operatorChar :: Tokenizer Char
    operatorChar = MP.satisfy isOperatorChar

    tokens :: Tokenizer [Locd (Tok 'Unbrack)]
    tokens = many token

    word :: Tokenizer Text
    word = T.cons <$> wordStart <*> (T.pack <$> many wordChar)

    operator :: Tokenizer Text
    operator = T.pack <$> some operatorChar

    locdword :: Tokenizer (Locd Text)
    locdword = ML.lexeme silence $ locd word

    locdop :: Tokenizer (Locd Text)
    locdop = ML.lexeme silence $ locd operator

    token :: Tokenizer (Locd (Tok 'Unbrack))
    token = asum
      [ locdsymNot operatorChar "<" $ Word $ Unqual Infix "<"
      , locdsym' "<"      $ AngleBegin ASCII
      , locdsym' "\x27E8" $ AngleBegin Unicode
      , locdsymNot operatorChar ">" $ Word $ Unqual Infix ">"
      , locdsym' ">"      $ AngleEnd ASCII
      , locdsym' "\x27E9" $ AngleEnd Unicode
      , locdsym' "\x27E6" $ ArrayBegin Unicode
      -- TODO: operators containing |
      , locdsym' "|]"     $ ArrayEnd ASCII
      , locdsym' "\x27E7" $ ArrayEnd Unicode
      , locdsymNot operatorChar "->" $ Arrow ASCII
      , locdsymNot operatorChar "\x2192" $ Arrow Unicode
      -- "{" and "{|"
      , do
        _ :@ brackLoc <- locd $ MC.string "{"
        bar <- optional $ locd $ MC.string "|"
        _ <- silence
        pure case bar of
          Just (_ :@ barLoc) -> UnboxedBegin ASCII :@ (brackLoc <> barLoc)
          Nothing -> BlockBegin :@ brackLoc
      , locdsym' "}"      BlockEnd
      , locdsym' "..."    $ Ellipsis ASCII
      , locdsym' "\x2026" $ Ellipsis Unicode
      , locdsym' "("      GroupBegin
      , locdsym' ")"      GroupEnd
      , locdsymNot wordChar "_" Ignore
      -- ":" and "::"
      , do
        _ :@ firstLoc <- locd $ MC.string ":"
        second <- optional $ locd $ MC.string ":"
        _ <- silence
        pure case second of
          Just (_ :@ secondLoc) -> Look ASCII :@ (firstLoc <> secondLoc)
          Nothing -> Layout :@ firstLoc
      -- "[" and "[|"
      , do
        _ :@ brackLoc <- locd $ MC.string "["
        bar <- optional $ locd $ MC.string "|"
        _ <- silence
        pure case bar of
          Just (_ :@ barLoc) -> ArrayBegin ASCII :@ (brackLoc <> barLoc)
          Nothing -> ListBegin :@ brackLoc
      , locdsym' "]"      ListEnd
      , locdsym' "\x2237" $ Look Unicode
      -- TODO: character literals
      , locdsym' "''"     Quote
      , locdsymNot operatorChar "\\" Ref
      , locdsym' ","      Seq
      , locdsymNot operatorChar "#" Splice
      , locdsym' ";"      Term
      , locdsym' "\x2983" $ UnboxedBegin Unicode
      -- TODO: operators containing |
      , locdsym' "|}"     $ UnboxedEnd ASCII
      , locdsym' "\x2984" $ UnboxedEnd Unicode

      , locdkwd' "about"      KwdAbout
      , locdkwd' "as"         KwdAs
      , locdkwd' "case"       KwdCase
      , locdkwd' "define"     KwdDefine
      , locdkwd' "do"         KwdDo
      , locdkwd' "elif"       KwdElif
      , locdkwd' "else"       KwdElse
      , locdkwd' "export"     KwdExport
      , locdkwd' "export"     KwdExport
      , locdkwd' "if"         KwdIf
      , locdkwd' "import"     KwdImport
      , locdkwd' "instance"   KwdInstance
      , locdkwd' "intrinsic"  KwdIntrinsic
      , locdkwd' "jump"       KwdJump
      , locdkwd' "match"      KwdMatch
      , locdkwd' "loop"       KwdLoop
      , locdkwd' "permission" KwdPermission
      , locdkwd' "return"     KwdReturn
      , locdkwd' "synonym"    KwdSynonym
      , locdkwd' "trait"      KwdTrait
      , locdkwd' "type"       KwdType
      , locdkwd' "vocab"      KwdVocab
      , locdkwd' "with"       KwdWith

      , fmap (Word . Unqual Infix) <$> locdop
      , fmap (Word . Unqual Postfix) <$> locdword
      ]

-- | Convert a stream of tokens with layout-sensitive blocks into one that uses
-- explicit brackets and terminators.
--
-- A layout block consists of a colon followed by one or more lines whose source
-- column is greater than the indentation of the line containing the colon. Each
-- line consists of one or more items whose source column is greater than that
-- of the first item in the line. Each item is either a non-bracket token, or a
-- series of items between bracket tokens.
--
-- Lines are desugared with terminators between them, and layout blocks are
-- desugared with explicit block delimiters around them. For example:
--
-- > outer:
-- >   inner1:
-- >     line1 line1
-- >       line1
-- >     line2
-- >       line2
-- >       line2
-- >   inner2:
-- >     line3 line3
-- >     line4
-- >       line4
--
-- Becomes:
--
-- > outer{
-- >   inner1{
-- >     line1 line1
-- >       line1;
-- >     line2
-- >       line2
-- >       line2;};
-- >   inner2{
-- >     line3 line3;
-- >     line4
-- >       line4;};}
--
-- Note that if a block uses explicit braces, its contents are /not/ interpreted
-- as folded lines, and no terminators will be inserted.
--
bracket :: SrcName -> [Locd (Tok 'Unbrack)] -> [Locd (Tok 'Brack)]
bracket srcName tokens = case MP.runParser bracketer (show srcName) indented of
  Left err -> error $ concat
    [ "internal bracketing error: "
    , MP.errorBundlePretty err
    ]
  Right result -> result
  where
    indented = concat $ zipWith indentEach indents rows
    indentEach indent line = (:> indent) <$> line
    indents = locBeginCol . locdLoc . head <$> rows
    rows = groupBy ((==) `on` locBeginRow . locdLoc) tokens

    bracketer :: Bracketer [Locd (Tok 'Brack)]
    bracketer = concat <$> many item <* MP.eof

    item :: Bracketer [Locd (Tok 'Brack)]
    item = itemWhere $ const True

    itemWhere
      :: (Indented (Locd (Tok 'Unbrack)) -> Bool)
      -> Bracketer [Locd (Tok 'Brack)]
    itemWhere p = MP.try (MP.lookAhead (MP.satisfy p)) *> asum
      [ between (ArrayBegin ASCII) (ArrayEnd ASCII)
      , between (ArrayBegin Unicode) (ArrayEnd Unicode)
      , between (UnboxedBegin ASCII) (UnboxedEnd ASCII)
      , between (UnboxedBegin Unicode) (UnboxedEnd Unicode)
      , between BlockBegin BlockEnd
      , between GroupBegin GroupEnd
      , between ListBegin ListEnd
      , layout
      , pure <$> (fromUnbrack . indentedItem =<< MP.satisfy nonbracket)
      ]

    between :: Tok 'Unbrack -> Tok 'Unbrack -> Bracketer [Locd (Tok 'Brack)]
    between open close = do
      begin <- fromUnbrack . indentedItem =<< MP.satisfy ((== open) . locdItem . indentedItem)
      inner <- concat <$> many item
      end <- fromUnbrack . indentedItem =<< MP.satisfy ((== close) . locdItem . indentedItem)
      pure (begin : inner ++ [end])

    fromUnbrack :: Locd (Tok 'Unbrack) -> Bracketer (Locd (Tok 'Brack))
    fromUnbrack (tok :@ loc) = (:@ loc) <$> case tok of
      KwdAbout -> pure KwdAbout
      KwdAs -> pure KwdAs
      KwdCase -> pure KwdCase
      KwdDefine -> pure KwdDefine
      KwdDo -> pure KwdDo
      KwdElif -> pure KwdElif
      KwdElse -> pure KwdElse
      KwdExport -> pure KwdExport
      KwdIf -> pure KwdIf
      KwdImport -> pure KwdImport
      KwdInstance -> pure KwdInstance
      KwdIntrinsic -> pure KwdIntrinsic
      KwdJump -> pure KwdJump
      KwdMatch -> pure KwdMatch
      KwdLoop -> pure KwdLoop
      KwdPermission -> pure KwdPermission
      KwdReturn -> pure KwdReturn
      KwdSynonym -> pure KwdSynonym
      KwdTrait -> pure KwdTrait
      KwdType -> pure KwdType
      KwdVocab -> pure KwdVocab
      KwdWith -> pure KwdWith
      AngleBegin enc -> pure $ AngleBegin enc
      AngleEnd enc -> pure $ AngleEnd enc
      ArrayBegin enc -> pure $ ArrayBegin enc
      ArrayEnd enc -> pure $ ArrayEnd enc
      Arrow enc -> pure $ Arrow enc
      BlockBegin -> pure BlockBegin
      BlockEnd -> pure BlockEnd
      Ellipsis enc -> pure $ Ellipsis enc
      GroupBegin -> pure $ GroupBegin
      GroupEnd -> pure GroupEnd
      Ignore -> pure Ignore
      Layout -> pure $ BrackErr
        (T.pack (PP.render $ pPrint tok))
        "start of invalid layout block"
      ListBegin -> pure ListBegin
      ListEnd -> pure ListEnd
      Look enc -> pure $ Look enc
      Quote -> pure Quote
      Ref -> pure Ref
      Seq -> pure Seq
      Splice -> pure Splice
      Term -> pure Term
      UnboxedBegin enc -> pure $ UnboxedBegin enc
      UnboxedEnd enc -> pure $ UnboxedEnd enc
      Char enc lit -> pure $ Char enc lit
      Float lit -> pure $ Float lit
      Integer lit -> pure $ Integer lit
      Para enc lit -> pure $ Para enc lit
      Text enc lit -> pure $ Text enc lit
      Word name -> pure $ Word name
      TokErr src msg -> pure $ TokErr src msg

    nonbracket :: Indented (Locd (Tok 'Unbrack)) -> Bool
    nonbracket = not . (`elem` bracks') . locdItem . indentedItem

    bracks' :: [Tok 'Unbrack]
    bracks' = uncurry (++) $ unzip $ M.toList bracks

    bracks :: Map (Tok 'Unbrack) (Tok 'Unbrack)
    bracks = M.fromList
      [ (ArrayBegin ASCII, ArrayEnd ASCII)
      , (ArrayBegin Unicode, ArrayEnd Unicode)
      , (BlockBegin, BlockEnd)
      , (GroupBegin, GroupEnd)
      , (ListBegin, ListEnd)
      , (UnboxedBegin ASCII, UnboxedEnd ASCII)
      , (UnboxedBegin Unicode, UnboxedEnd Unicode)
      ]

    layout :: Bracketer [Locd (Tok 'Brack)]
    layout = do
      (_ :@ colonLoc) :> colonIndent <- MP.satisfy
        $ (== Layout) . locdItem . indentedItem
      asum
        [ do
          body <- some $ layoutLine colonIndent
          let
            -- Calculate the source location just past the end of the last token.
            pastEnd toks = let
              lastLoc = locdLoc $ last toks
              lastCol = locEndCol lastLoc
              in lastLoc { locBeginCol = lastCol, locEndCol = lastCol }
            endLoc = pastEnd $ concat body
            body' = concat $ (\ line -> let
              termLoc = pastEnd line
              in line ++ [Term :@ termLoc]) <$> body
          pure $ (BlockBegin :@ colonLoc) : body' ++ [BlockEnd :@ endLoc]
        -- A layout block always consumes a colon before yielding a tombstone
        -- for an empty layout block; if this were in 'itemWhere', it would
        -- always produce an error tombstone, leading to an infinite loop since
        -- it's called from 'many' and consumes no input.
        , do
          loc <- getSourceLoc
          pure $ pure $ (:@ loc) $ BrackErr "" "empty layout block"
        ]

    layoutLine :: Col -> Bracketer [Locd (Tok 'Brack)]
    layoutLine colonIndent = do
      (first@(_ :@ firstLoc) :> _) <- MP.satisfy
        $ (> colonIndent) . locBeginCol . locdLoc . indentedItem
      rest <- fmap concat $ many $ itemWhere
        $ (> locBeginCol firstLoc) . locBeginCol . locdLoc . indentedItem
      first' <- fromUnbrack first
      pure $ first' : rest

instance MP.Stream [Indented (Locd (Tok 'Unbrack))] where
  type Token [Indented (Locd (Tok 'Unbrack))] = Indented (Locd (Tok 'Unbrack))
  type Tokens [Indented (Locd (Tok 'Unbrack))] = [Indented (Locd (Tok 'Unbrack))]
  tokenToChunk Proxy = pure
  tokensToChunk Proxy = id
  chunkToTokens Proxy = id
  chunkLength Proxy = length
  chunkEmpty Proxy = null
  take1_ [] = Nothing
  take1_ (t:ts) = Just (t, ts)
  takeN_ n s
    | n <= 0 = Just ([], s)
    | null s = Nothing
    | otherwise = Just $ splitAt n s
  takeWhile_ = span
  showTokens Proxy = PP.render . PP.hsep
    . fmap (pPrint . locdItem . indentedItem) . toList
  reachOffset = reachOffset' (locdLoc . indentedItem) splitAt foldl'

instance MP.Stream [Locd (Tok 'Brack)] where
  type Token [Locd (Tok 'Brack)] = Locd (Tok 'Brack)
  type Tokens [Locd (Tok 'Brack)] = [Locd (Tok 'Brack)]
  tokenToChunk Proxy = pure
  tokensToChunk Proxy = id
  chunkToTokens Proxy = id
  chunkLength Proxy = length
  chunkEmpty Proxy = null
  take1_ [] = Nothing
  take1_ (t:ts) = Just (t, ts)
  takeN_ n s
    | n <= 0 = Just ([], s)
    | null s = Nothing
    | otherwise = Just $ splitAt n s
  takeWhile_ = span
  showTokens Proxy = PP.render . PP.hsep
    . fmap (pPrint . locdItem) . toList
  reachOffset = reachOffset' locdLoc splitAt foldl'

reachOffset'
  :: forall s
  . (MP.Stream s, Show (MP.Tokens s), Pretty (MP.Token s))
  => (MP.Token s -> Loc)
  -> (Int -> s -> (MP.Tokens s, s))
  -> (forall b. (b -> MP.Token s -> b) -> b -> MP.Tokens s -> b)
  -> Int
  -> MP.PosState s
  -> (MP.SourcePos, String, MP.PosState s)
reachOffset' locOf splitAt' foldl'' o state =
  ( spos
  , case addPrefix . f $ takeSameLine post of
    "" -> "<empty line>"
    xs -> xs
  , MP.PosState
    { MP.pstateInput = post
    , MP.pstateOffset = MP.pstateOffset state `max` o
    , MP.pstateSourcePos = spos
    , MP.pstateTabWidth = MP.pstateTabWidth state
    , MP.pstateLinePrefix = (if sameLine then (MP.pstateLinePrefix state ++) else id) (f "")
    }
  )
  where
    takeSameLine :: s -> String
    takeSameLine s
      | Just (x, _xs) <- MP.take1_ s
      = PP.render $ PP.hsep $ fmap pPrint $ MP.chunkToTokens (Proxy @s)
        $ fst $ MP.takeWhile_ ((== locBeginRow (locOf x)) . locBeginRow . locOf) s
      | otherwise = ""

    addPrefix xs = if sameLine then MP.pstateLinePrefix state ++ xs else xs
    sameLine = MP.sourceLine spos == MP.sourceLine (MP.pstateSourcePos state)
    (pre, post) = splitAt' (o - MP.pstateOffset state) (MP.pstateInput state)
    (spos, f) = foldl'' go (MP.pstateSourcePos state, id) pre
    go (MP.SourcePos n l c, g) ch =
      ( MP.SourcePos n l (c <> MP.mkPos (colVal (locEndCol loc) - colVal (locBeginCol loc) + 1))
      , g . ((PP.render (pPrint ch) ++ " ") ++)
      )
      where
        loc = locOf ch

-- | Parse a stream of bracketed tokens into a program fragment.
parse :: SrcName -> [Locd (Tok 'Brack)] -> Frag [] 'Parsed
parse srcName tokens = case MP.runParser parser (show srcName) tokens of
  Left err -> error $ concat
    [ "internal parsing error: "
    , MP.errorBundlePretty err
    ]
  Right result -> result
  where

    -- <program>
    --   ::= <vocab>*
    parser :: Parser (Frag [] 'Parsed)
    parser = partitionElems . (flattenVocabTree =<<) <$> many vocab <* MP.eof

    -- <vocab>
    --   ::= "vocab" <vocab-name> "{" <vocab>* "}"
    --     | "vocab" <vocab-name> ";" <vocab>*
    --     | "vocab" "synonym" <vocab-name> "(" <name> ")" ";"
    --     | <elem>
    vocab :: Parser (VocabTree 'Parsed)
    vocab = asum
      [ do
        loc <- locdLoc <$> match KwdVocab
        asum
          [ VocabLeaf <$> do
            name <- match KwdSynonym *> vocabRelName
            syn <- grouped unresName <* match Term
            pure $ VocabSynElem VocabSyn
              { vocabSynLoc = loc
              , vocabSynName = name
              , vocabSynOf = syn
              }
          -- TODO: Don't backtrack over the whole name.
          , MP.try do
            name <- vocabRelName
            VocabRelBranch name <$> blocked (many vocab)
          , do
            name <- vocabAbsName <* match Term
            VocabAbsBranch name <$> many vocab
          ]
      , do
        VocabLeaf <$> element
      ]

    vocabRelName :: Parser (Vocab 'Rel)
    vocabRelName = VocabRel . V.fromList <$> namePart `MP.sepBy1` look

    postfixName :: Parser Unqual
    postfixName = extract (S.fromList [ME.Label ('p':|"ostfix name")]) \ case
      Word name@(Unqual Postfix _) :@ _ -> Just name
      _ -> Nothing

    infixName :: Parser Unqual
    infixName = extract (S.fromList [ME.Label ('i':|"nfix name")]) \ case
      Word name@(Unqual Infix _) :@ _ -> Just name
      _ -> Nothing

    bareName :: Parser Unqual
    bareName = postfixName <|> infixName

    namePart :: Parser Unqual
    namePart = postfixName <|> grouped infixName

    -- extract :: (Locd (Tok 'Brack) -> Maybe a) -> Parser a
    -- TODO: Use non-empty set of expected items.
    extract = flip MP.token

    vocabAbsName :: Parser (Vocab 'Abs)
    vocabAbsName = optional global
      *> (VocabAbs . V.fromList <$> namePart `MP.sepBy1` look)

    -- <name>
    --   ::= ("_" "::")? (<name-part> "::")* <name-part>
    unresName :: Parser Unres
    unresName = do
      mGlobal <- optional global
      prefix <- fmap V.fromList $ many $ MP.try $ namePart <* look
      if V.null prefix
        then UnresUnqual <$> (bareName <|> grouped infixName)
        else case mGlobal of
          Just{} -> UnresQualAbs . Qual (VocabAbs prefix) <$> namePart
          Nothing -> UnresQualRel . Qual (VocabRel prefix) <$> namePart

    -- <elem>
    --   ::= <inst-def>
    --     | <meta-def>
    --     | <perm-elem>
    --     | <trait-elem>
    --     | <type-elem>
    --     | <word-elem>
    --     | <term>
    element :: Parser (Elem 'Parsed)
    element = asum
      [ InstElem <$> instDef
      , MetaElem <$> metaDef
      , (PermElem ||| PermSynElem) <$> permElem
      , (TraitElem ||| TraitSynElem) <$> traitElem
      , (TypeElem ||| TypeSynElem) <$> typeElem
      , (WordElem ||| WordSynElem) <$> wordElem
      , TermElem <$> term
      ]

    -- <inst-def>
    --   ::= "instance" <qual> <sig> "{" <term>* "}"
    --     | "instance" <qual> <sig> ";"
    instDef :: Parser (InstDef 'Parsed)
    instDef = MP.label "instance definition" do
      _ :@ loc <- match KwdInstance
      InstDef loc <$> unresName <*> signature <*> optBlocked expr

    -- <meta-def>
    --   ::= "about" <qual> "{" <kvp>* "}"
    --     | "about" "instance" <qual> "{" <kvp>* "}"
    --     | "about" "permission" <qual> "{" <kvp>* "}"
    --     | "about" "trait" <qual> "{" <kvp>* "}"
    --     | "about" "type" <qual> "{" <kvp>* "}"
    --     | "about" "vocab" <qual> "{" <kvp>* "}"
    metaDef :: Parser (MetaDef 'Parsed)
    metaDef = mzero  -- error "TODO: metaDef"

    -- <perm-elem>
    --   ::= <perm-def>
    --     | <perm-syn>
    --
    -- <perm-def>
    --   ::= "permission" <qual> <sig> ";"
    --     | "permission" <qual> <sig> "{" <term>* "}"
    --
    -- <perm-syn>
    --   ::= "permission" "synonym" <qual> "(" <permit>* ")" ";"
    permElem :: Parser (PermDef 'Parsed + PermSyn 'Parsed)
    permElem = do
      _ :@ loc <- match KwdPermission
      match KwdSynonym *> (Right <$> permSyn loc) <|> Left <$> permDef loc
      where

        permSyn :: Loc -> Parser (PermSyn 'Parsed)
        permSyn loc = MP.label "permission synonym"
          $ PermSyn loc <$> unresName
            <*> (V.fromList <$> grouped (many permit))

        permDef :: Loc -> Parser (PermDef 'Parsed)
        permDef loc = MP.label "permission definition"
          $ PermDef loc <$> unresName <*> optBlocked expr

    -- <trait-elem>
    --   ::= <trait-def>
    --     | <trait-syn>
    --
    -- <trait-def>
    --   ::= "trait" <qual> <sig> ";"
    --     | "trait" <qual> <sig> "{" <term>* "}"
    --
    -- <trait-syn>
    --   ::= "trait" "synonym" <qual> "(" seq(<app-sig>) ")" ";"
    traitElem :: Parser (TraitDef 'Parsed + TraitSyn 'Parsed)
    traitElem = do
      _ :@ loc <- match KwdTrait
      match KwdSynonym *> (Right <$> traitSyn loc) <|> Left <$> traitDef loc
      where

        traitSyn :: Loc -> Parser (TraitSyn 'Parsed)
        traitSyn loc = MP.label "trait synonym"
          $ TraitSyn loc <$> unresName
            <*> (V.fromList <$> grouped (traitApp `MP.sepEndBy` match Seq))

        traitDef :: Loc -> Parser (TraitDef 'Parsed)
        traitDef loc = MP.label "trait definition"
          $ TraitDef loc <$> unresName <*> signature <*> optBlocked expr

    traitApp :: Parser (Constraint 'Parsed)
    traitApp = MP.label "trait constraint" do
      (prefix, suffixes) <- appType unresName
      guard (not (null suffixes))
      pure $ Constraint prefix (V.fromList suffixes)

    -- <type-elem>
    --   ::= <type-def>
    --     | <type-syn>
    --
    -- <type-def>
    --   ::= "type" <qual> <quant>? "{" <case>* "}"
    --
    -- <type-syn>
    --   ::= "type" "synonym" <qual> <quant>? "(" <sig> ")" ";"
    typeElem :: Parser (TypeDef 'Parsed + TypeSyn 'Parsed)
    typeElem = do
      _ :@ loc <- match KwdType
      match KwdSynonym *> (Right <$> typeSyn loc) <|> Left <$> typeDef loc
      where

        typeSyn :: Loc -> Parser (TypeSyn 'Parsed)
        typeSyn loc = MP.label "type synonym"
          $ TypeSyn loc <$> unresName <*> grouped signature <* match Term

        typeDef :: Loc -> Parser (TypeDef 'Parsed)
        typeDef loc = MP.label "type definition"
          $ TypeDef loc <$> unresName <*> optional quant
            <*> (maybe mempty V.fromList
              <$> optBlocked (caseDef `MP.sepEndBy` match Term))

        caseDef :: Parser (CaseDef 'Parsed)
        caseDef = MP.label "case definition"
          $ CaseDef <$> (locdLoc <$> match KwdCase) <*> bareName
            <*> optional quant <*> optional fields

        fields :: Parser (CaseFields 'Parsed)
        fields = asum
          [ MP.label "anonymous field list" do
            _ :@ beginLoc <- match GroupBegin
            sigs <- (basicType <|> signature) `MP.sepEndBy` match Seq
            _ :@ endLoc <- match GroupEnd
            pure $ AnonFields (beginLoc <> endLoc) $ V.fromList sigs
          , MP.label "named field block" do
            _ :@ beginLoc <- match BlockBegin
            sigs <- V.fromList <$> field `MP.sepEndBy` match Term
            _ :@ endLoc <- match BlockEnd
            pure $ NamedFields (beginLoc <> endLoc) sigs
          ]
          where
            field :: Parser (Unqual, Sig 'Parsed)
            field = (,)
              <$> (postfixName <* match KwdAs)
              <*> (basicType <|> signature)

    -- <word-elem>
    --   ::= <word-def>
    --     | <word-syn>
    --
    -- <word-def>
    --   ::= "define" <qual> <sig> "{" <term>* "}"
    --
    -- <word-syn>
    --   ::= "synonym" <qual> <quant>? "(" <instantiated-name> ")" ";"
    wordElem :: Parser (WordDef 'Parsed + WordSyn 'Parsed)
    wordElem = Left <$> wordDef <|> Right <$> wordSyn
      where

        wordDef :: Parser (WordDef 'Parsed)
        wordDef = MP.label "word definition" do
          _ :@ loc <- match KwdDefine
          WordDef loc <$> unresName <*> signature <*> blocked expr

        wordSyn :: Parser (WordSyn 'Parsed)
        wordSyn = MP.label "word synonym" do
          _ :@ loc <- match KwdSynonym
          WordSyn loc <$> unresName <*> optional quant
            <*> (grouped instdName <* match Term)

    signature :: Parser (Sig 'Parsed)
    signature = MP.label "type signature"
      $ quantified (grouped functionType)
      <|> grouped functionType

    functionType :: Parser (Sig 'Parsed)
    functionType = MP.label "function type" do
      effect <- asum
        [ MP.label "stack-polymorphic function type" do
          l :@ ll <- stack
          ls <- fromMaybe [] <$> optional (match Seq *> left)
          r :@ rl <- arrow *> stack
          rs <- fromMaybe [] <$> optional (match Seq *> right)
          let
            loc = case concat
              [ (^. location) <$> ls
              , (^. location) <$> rs
              ] of
              [] -> ll <> rl
              (x:xs) -> ll <> sconcat (x :| xs) <> rl
          pure $ StackSig loc l (V.fromList ls) r (V.fromList rs)
        , MP.label "basic function type" do
          ls <- left
          _ :@ al <- arrow
          rs <- right
          let loc = sconcat $ al :| ((^. location) <$> ls) <> ((^. location) <$> rs)
          pure $ FunSig loc (V.fromList ls) (V.fromList rs)
        ]
      permits <- MP.label "permission labels" $ V.fromList <$> many permit
      pure $ effect permits
      where

        stack :: Parser (Locd Unqual)
        stack = do
          sigilLoc <- getSourceLoc <* ellipsis
          (nameLoc, name) <- (,) <$> getSourceLoc <*> postfixName
          pure (name :@ (sigilLoc <> nameLoc))

        left, right :: Parser [Sig 'Parsed]
        left = basicType `MP.sepEndBy` match Seq
        right = type_ `MP.sepEndBy` match Seq

    permit :: Parser (Permit 'Parsed)
    permit = Grant <$> (match (Word (Unqual Infix "+")) *> unresName)
      <|> Revoke <$> (match (Word (Unqual Infix "-")) *> unresName)

    basicType :: Parser (Sig 'Parsed)
    basicType = MP.label "basic type" do
      (prefix, suffixes) <- appType $ asum
        [ quantified (basicType <|> grouped type_)
        , MP.try do
          loc <- getSourceLoc
          name <- unresName
          pure $ VarSig loc name
        , grouped type_
        ]
      pure $ foldl' applyTypes prefix suffixes

    applyTypes :: Sig p -> Sig p -> Sig p
    applyTypes ty args = AppSig ((ty ^. location) <> (args ^. location)) ty args

    appType :: Parser a -> Parser (a, [Sig 'Parsed])
    appType ty = MP.label "type application"
      $ (,) <$> ty <*> (concat <$> many typeList)

    type_ :: Parser (Sig 'Parsed)
    type_ = MP.label "type" $ MP.try functionType <|> basicType

    -- <instd>
    --   ::= <name> ("::" "<" <sig> ("," <sig>)* ">")?
    instdName :: Parser (Instd 'Parsed)
    instdName = MP.label "instantiated name" $ Instd
      <$> unresName
      <*> (MP.label "type arguments" $ V.fromList . fromMaybe []
        <$> optional (look *> typeList))

    typeList :: Parser [Sig 'Parsed]
    typeList = angled (type_ `MP.sepEndBy1` match Seq)

    quant :: Parser (Quant 'Parsed)
    quant = MP.label "quantifier" do
      -- TODO: Compute full source location.
      loc <- getSourceLoc
      MP.label "universal quantifier" (Forall loc <$> angled vars)
        <|> MP.label "existential quantifier" (Exists loc <$> bracketed vars)
      where
        vars = V.fromList <$> (var `MP.sepEndBy1` match Seq)

    quantified :: Parser (Sig 'Parsed) -> Parser (Sig 'Parsed)
    quantified p = do
      q <- quant
      t <- p
      pure $ QuantSig ((q ^. location) <> (t ^. location)) q t

    -- <var>
    --   ::= <kind-sigil>? <postfix-name> <var-type-params>?
    --     | <postfix-name> "as" <sig>
    --
    -- <kind-sigil>
    --   ::= "..." | "+"
    --
    -- <var-type-params>
    --   ::= "<" <var-type-param> ("," <var-type-param>)* ">"
    --
    -- <var-type-param>
    --   ::= <kind-sigil>? <postfix-name> <var-type-params>?
    --     | <kind-sigil>? "_" <var-type-params>?
    --
    -- Examples:
    --
    --     Type
    --     +Permission
    --     ...Stack
    --     Functor<Type>
    --     Functor<_>
    --     Profunctor<A, B>
    --     Profunctor<_, _>
    --     Transformer<Monad<_>, T>
    --     FunctionLike<..._, ..._, +_>
    --     +ParameterizedPermission<_>
    --     T as type
    --     P as permission
    --     S as stack
    --     N as Size
    --     Functor as type -> type
    --     FunctionLike as stack -> stack -> permission -> type
    --
    var :: Parser (Var 'Parsed)
    var = MP.label "type parameter"
      $ uncurry Var <$> var' (MP.label "type variable name" postfixName)
      where
        var' :: Parser n -> Parser (n, Kind 'Parsed)
        var' identifier = do
          sigil <- optional kindSigil
          name <- identifier
          asum
            [ do
              kinds <- match KwdAs *> (kindName `MP.sepBy1` arrow)
              pure (name, foldr1 FunKind kinds)
            , do
              params <- fmap snd . fromMaybe [] <$> optional
                (angled (var' (void ignore <|> void postfixName) `MP.sepEndBy1` match Seq))
              let kind = fromMaybe ValueKind sigil
              pure (name, foldr FunKind kind params)
            ]

        kindSigil = MP.label "kind sigil" $ asum
          [ StackKind <$ match (Ellipsis ASCII)
          , StackKind <$ match (Ellipsis Unicode)
          , PermKind <$ match (Word (Unqual Infix "+"))
          ]

    kindName :: Parser (Kind 'Parsed)
    kindName = MP.label "kind name" $ asum
      [ ValueKind <$ match KwdType
      , PermKind <$ match KwdPermission
      , StackKind <$ match (Word (Unqual Postfix "stack"))
      , TypeKind <$> unresName
      ]

    -- <term>
    --   ::= <term> "as" <sig>
    --     | "(" "as" seq(<sig>) ")"
    --     | "call"
    --     | "do" "(" <term>* ")" "{" <term>* "}"
    --     | "(" <term>* ")"
    --     |
    --     | "if" ("(" <term>* ")")? "{" <term>* "}"
    --       ("elif" "(" <term>* ")" "{" <term>* "}")*
    --       ("else" "{" <term>* "}")?
    --     | <instantiated-name>
    --     | "(" <op> ")"
    --     | "jump"
    --     | "[" seq(<term>*) "]"
    --     | "[|" seq(<term>*) "|]"
    --     | "loop"
    --     | "match" ("(" <term>* ")")?
    --       ("case" <pat> <block>)*
    --       ("else" "{" <term>* "}")?
    --     | <term>* <op> <term>*
    --     | <char-lit>
    --     | <float-lit>
    --     | <int-lit>
    --     | <para-lit>
    --     | <text-lit>
    --     | "{" <term>* "}"
    --     | "{|" <term>* "|}"
    --     | "\" <term>
    --     | "return"
    --     | "(" <op> <term>* ")"
    --     | "(" <term>* <op> ")"
    term :: Parser (Term 'Parsed)
    term = MP.failure Nothing (S.fromList [ME.Label ('T':|"ODO: parse term")])  -- error "TODO: term"

    expr :: Parser (Term 'Parsed)
    expr = do
      loc <- getSourceLoc
      foldl' (Compose ()) (Identity () loc) <$> many term

    match :: Tok 'Brack -> Parser (Locd (Tok 'Brack))
    match tok = MP.label (PP.render (pPrint tok))
      $ MP.satisfy ((== tok) . locdItem)

    grouped :: Parser a -> Parser a
    grouped = (match GroupBegin *>) . (<* match GroupEnd)

    blocked :: Parser a -> Parser a
    blocked = (match BlockBegin *>) . (<* match BlockEnd)

    optBlocked :: Parser a -> Parser (Maybe a)
    optBlocked p = Nothing <$ match Term <|> Just <$> blocked p

    bracketed :: Parser a -> Parser a
    bracketed = (match ListBegin *>) . (<* match ListEnd)

    angled :: Parser a -> Parser a
    angled p
      = (match (AngleBegin ASCII) <|> match (Word (Unqual Infix "<")))
        *> p
        <* (match (AngleEnd ASCII) <|> match (Word (Unqual Infix ">")))
      <|> match (AngleBegin Unicode) *> p <* match (AngleEnd Unicode)

    arrow, ellipsis, global, ignore, look :: Parser (Locd (Tok 'Brack))
    arrow = match (Arrow ASCII) <|> match (Arrow Unicode)
    ellipsis = match (Ellipsis ASCII) <|> match (Ellipsis Unicode)
    global = ignore *> look
    ignore = match Ignore
    look = match (Look ASCII) <|> match (Look Unicode)

    partitionElems :: [Elem 'Parsed] -> Frag [] 'Parsed
    partitionElems = foldr (flip go) emptyFrag
      where
        go :: Frag [] 'Parsed -> Elem 'Parsed -> Frag [] 'Parsed
        go f@Frag{..} = \ case
          InstElem x -> f { fragInsts = x : fragInsts }
          MetaElem x -> f { fragMetas = x : fragMetas }
          PermSynElem x -> f { fragPermSyns = x : fragPermSyns }
          PermElem x -> f { fragPerms = x : fragPerms }
          TermElem x -> f { fragTerms = x : fragTerms }
          TraitSynElem x -> f { fragTraitSyns = x : fragTraitSyns }
          TraitElem x -> f { fragTraits = x : fragTraits }
          TypeSynElem x -> f { fragTypeSyns = x : fragTypeSyns }
          TypeElem x -> f { fragTypes = x : fragTypes }
          VocabSynElem x -> f { fragVocabSyns = x : fragVocabSyns }
          WordSynElem x -> f { fragWordSyns = x : fragWordSyns }
          WordElem x -> f { fragWords = x : fragWords }

getSourceLoc :: (MP.Stream [t]) => MP.Parsec Void [t] Loc
getSourceLoc = join locRange <$> MP.getSourcePos

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

--------------------------------------------------------------------------------

(.||.) :: (Monad f) => f Bool -> f Bool -> f Bool
f .||. g = do
  x <- f
  if x then pure True else g
infixr 2 .||.

(.&&.) :: (Monad f) => f Bool -> f Bool -> f Bool
f .&&. g = do
  x <- f
  if x then g else pure False
infixr 3 .&&.

floatLitVal :: Fractional a => FloatLit -> a
floatLitVal (FloatLit sig frac ex _bits)
  = fromRational $ (fromIntegral sig :: Rational) * shift
  where
    delta = ex - frac
    shift
      | delta < 0 = 1 % 10 ^ negate delta
      | otherwise = 10 ^ delta

isOperatorChar :: Char -> Bool
isOperatorChar = (isSymbol .||. isPunctuation) .&&. (`notElem` reservedSymChars)

-- | List of symbol characters that cannot appear in an operator name.
--
-- Note that the following characters /are/ allowed in operators despite having
-- special meaning as lexical symbols:
--
-- * @<@
-- * @>@
-- * @|@
-- * @:@
-- * U+2192 RIGHTWARDS ARROW
-- * @.@
-- * U+2026 HORIZONTAL ELLIPSIS
-- * @\\@
-- * @#@
--
reservedSymChars :: [Char]
reservedSymChars =
  [ '\x27E8' -- U+27E8 MATHEMATICAL LEFT ANGLE BRACKET
  , '\x27E9' -- U+27E9 MATHEMATICAL RIGHT ANGLE BRACKET
  , '\x27E6' -- U+27E6 MATHEMATICAL LEFT WHITE SQUARE BRACKET
  , '\x27E7' -- U+27E7 MATHEMATICAL RIGHT WHITE SQUARE BRACKET
  , '{'      -- U+007B LEFT CURLY BRACKET
  , '}'      -- U+007D RIGHT CURLY BRACKET
  , '('      -- U+0028 LEFT PARENTHESIS
  , ')'      -- U+0029 RIGHT PARENTHESIS
  , '_'      -- U+005F SPACING UNDERSCORE
  , '['      -- U+005B LEFT SQUARE BRACKET
  , ']'      -- U+005D RIGHT SQUARE BRACKET
  , '\x2237' -- U+2237 PROPORTION
  , '\''     -- U+0027 APOSTROPHE
  , '"'      -- U+0022 QUOTATION MARK
  , '\x201C' -- U+201C LEFT DOUBLE QUOTATION MARK
  , '\x201D' -- U+201D RIGHT DOUBLE QUOTATION MARK
  , '\x2018' -- U+2018 LEFT SINGLE QUOTATION MARK
  , '\x2019' -- U+2019 RIGHT SINGLE QUOTATION MARK
  , ','      -- U+002C COMMA
  , ';'      -- U+003B SEMICOLON
  , '\x2983' -- U+2983 LEFT WHITE CURLY BRACKET
  , '\x2984' -- U+2984 RIGHT WHITE CURLY BRACKET
  , '\x00B6' -- U+00B6 PILCROW SIGN
  ]

isWordChar :: Char -> Bool
isWordChar = isAlphaNum .||. isMark .||. (== '_')

isWordStart :: Char -> Bool
isWordStart = isAlpha .||. (== '_')

locd :: Tokenizer a -> Tokenizer (Locd a)
locd tok = do
  begin <- MP.getSourcePos
  result <- tok
  end <- MP.getSourcePos
  let loc = locRange begin end
  pure $ result :@ loc

locRange :: MP.SourcePos -> MP.SourcePos -> Loc
locRange a b = Loc
  { locName = case readMaybe $ MP.sourceName a of
    Just name -> name
    Nothing -> error $ concat
      [ "internal tokenizer error: invalid source name "
      , show (MP.sourceName a)
      ]
  , locBeginRow = Row $ MP.unPos $ MP.sourceLine a
  , locBeginCol = Col $ MP.unPos $ MP.sourceColumn a
  , locEndRow = Row $ MP.unPos $ MP.sourceLine b
  , locEndCol = Col $ MP.unPos $ MP.sourceColumn b
  }
