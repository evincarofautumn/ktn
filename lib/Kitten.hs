{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

#if __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE QuantifiedConstraints #-}
#endif

module Kitten
  ( Brack(..)
  , BrackErr(..)
  , Col(..)
  , Enc(..)
  , ErrMsg(..)
  , Fixity(..)
  , Indented(..)
  , Loc(..)
  , Locd(..)
  , Row(..)
  , SrcName(..)
  , Tok(..)
  , TokErr(..)
  , Unqual(..)
  , type (+)
  , bracket
  , tokenize
  ) where

import Control.Applicative (many, optional, some)
import Data.Char
import Data.Foldable (asum, toList)
import Data.Function (on)
import Data.Functor.Identity (Identity)
import Data.List (foldl', groupBy)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import Data.Ord (Down(..), comparing)
import Data.Proxy (Proxy(..))
import Data.Ratio ((%))
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Void (Void)
import GHC.Types (Type)
import Text.PrettyPrint.HughesPJClass (Pretty(..))
import Text.Read (readMaybe)
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MC
import qualified Text.Megaparsec.Char.Lexer as ML
import qualified Text.Megaparsec.Error as ME
import qualified Text.PrettyPrint as PP

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
  deriving (Show)

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

-- | A bracket inserter.
type Bracketer = MP.Parsec Void [Indented (Locd (Tok 'Unbrack))]

-- | The contents of a character literal.
data CharLit :: Type where
  CharLit :: !(Esc + Char) -> CharLit
  deriving (Eq, Ord, Show)

-- | A column in a source location.
newtype Col = Col { colVal :: Int }
  deriving (Enum, Eq, Ord, Show)

-- | The encoding of a token with both ASCII and Unicode spellings.
data Enc :: Type where
  ASCII :: Enc
  Unicode :: Enc
  deriving (Eq, Ord, Show)

-- | An error message.
newtype ErrMsg = ErrMsg Text
  deriving (Eq, Show)

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

-- | A value decorated with an indent level.
data Indented :: Type -> Type where
  (:>) ::
    { indentedItem :: a
    , indentedLevel :: !Col
    } -> Indented a
  deriving (Eq, Functor, Ord, Show)

infixl 6 :>

instance (ME.ShowToken a) => ME.ShowToken (Indented a) where
  showTokens = ME.showTokens . fmap indentedItem

-- | An instance definition.
data InstDef :: Phase -> Type where
  InstDef ::
    { instName :: !(Name p)
    , instSig :: !(Sig p)
    , instBody :: !(Maybe (Term p))
    } -> InstDef p

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
data Kind :: Type where
  StackKind :: Kind
  ValueKind :: Kind
  LabelKind :: Kind
  PermKind :: Kind
  FunKind :: !Kind -> !Kind -> Kind
  TypeKind :: !(Qual 'Abs) -> Kind
  deriving (Show)

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
  deriving (Eq, Show)

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
  (:@) ::
    { locdItem :: a
    , locdLoc :: !Loc
    } -> Locd a
  deriving (Eq, Functor, Ord, Show)

infixl 7 :@

instance (ME.ShowToken a) => ME.ShowToken (Locd a) where
  showTokens = ME.showTokens . fmap locdItem

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

-- | The contents of a paragraph literal.
data ParaLit :: Type where
  ParaLit :: !(Vector (Vector (Esc + Text))) -> ParaLit
  deriving (Eq, Ord, Show)

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
newtype Row = Row { rowVal :: Int }
  deriving (Eq, Ord, Show)

-- | A parsed type signature.
data Sig :: Phase -> Type where
  AppSig :: !(Sig p) -> !(Sig p) -> Sig p
  FunSig
    :: !(Vector (Sig p))
    -> !(Vector (Sig p))
    -> !(Vector (Name p))
    -> Sig p
  StackSig
    :: !Unqual
    -> !(Vector (Sig p))
    -> !Unqual
    -> !(Vector (Sig p))
    -> !(Vector (Name p))
    -> Sig p
  VarSig :: Name p -> Sig p
  ForallSig
    :: !(Vector Var)
    -> Sig p
    -> Sig p
  ExistsSig
    :: !(Vector Var)
    -> Sig p
    -> Sig p

deriving instance (Show (Name p)) => Show (Sig p)

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

deriving instance (Show (Anno p), Show (Name p)) => Show (Term p)

-- | An existential type variable in a type.
newtype TEVar = TEVar Var
  deriving (Show)

-- | The contents of a text literal.
data TextLit :: Type where
  TextLit :: !(Vector (Esc + Text)) -> TextLit
  deriving (Eq, Ord, Show)

-- | A token, indexed by a 'Brack'eting that indicates whether it has been
-- 'bracket'ed.
data Tok :: Brack -> Type where

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
  Lookup :: !Enc -> Tok b
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

  deriving (Eq, Ord, Show)

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
    Lookup ASCII -> "::"
    Lookup Unicode -> "\x2237"
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

instance ME.ShowToken (Tok b) where
  showTokens = PP.render . PP.hsep . fmap pPrint . toList

-- | A character tokenizer.
type Tokenizer = MP.Parsec Void Text

-- | A lexical error.
data TokErr :: Type where
  TokErr :: !(Locd Text) -> !ErrMsg -> TokErr
  deriving (Eq, Show)

-- | The definition of a trait.
data TraitDef :: Phase -> Type where
  TraitDef :: TraitDef p
  deriving (Show)

-- | The definition of a trait synonym.
data TraitSyn :: Phase -> Type where
  TraitSyn :: TraitSyn p
  deriving (Show)

-- | A type variable in a type.
newtype TVar = TVar Var
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
  deriving (Eq, Ord, Show)

instance Pretty Unqual where
  pPrint (Unqual _fixity name) = PP.text $ T.unpack name

-- | An unresolved name.
data Unres :: Type where
  UnresUnqual :: Unqual -> Unres
  UnresQualRel :: Qual 'Rel -> Unres
  UnresQualAbs :: Qual 'Abs -> Unres
  deriving (Show)

-- | A variable in a quantifier in a type signature.
data Var :: Type where
  Var :: !Unqual -> !Kind -> Var
  deriving (Show)

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
tokenize :: SrcName -> Row -> Text -> [Locd (TokErr + Tok 'Unbrack)]
tokenize srcName row input = case MP.runParser tokenizer name input of
  Left err -> error $ concat
    [ "internal tokenizer error: "
    , MP.parseErrorPretty err
    ]
  Right result -> result
  where
    name :: String
    name = show srcName

    firstLine :: MP.Pos
    firstLine = MP.mkPos $ rowVal row

    tokenizer :: Tokenizer [Locd (TokErr + Tok 'Unbrack)]
    tokenizer = do
      MP.setPosition (MP.SourcePos name firstLine MP.pos1)
      file

    file :: Tokenizer [Locd (TokErr + Tok 'Unbrack)]
    file = MP.between silence MP.eof tokens

    silence :: Tokenizer ()
    silence = ML.space MC.space1
      (ML.skipLineComment "//")
      (ML.skipBlockCommentNested "/*" "*/")

    locdsym :: Text -> Tokenizer (Locd Text)
    locdsym = ML.lexeme silence . locd . MC.string

    locdsym' :: Text -> Tok b -> Tokenizer (Locd (e + Tok b))
    locdsym' sym tok = (Right tok <$) <$> locdsym sym

    locdsymNot :: Tokenizer a -> Text -> Tok b -> Tokenizer (Locd (e + Tok b))
    locdsymNot not sym tok = MP.try $ fmap (fmap (Right . const tok))
      $ ML.lexeme silence $ locd $ MC.string sym <* MP.notFollowedBy (MP.try not)

    locdkwd :: Text -> Tokenizer (Locd Text)
    locdkwd = ML.lexeme silence . locd
      . (<* MP.notFollowedBy (MP.try wordChar)) . MC.string

    locdkwd' :: Text -> Tok b -> Tokenizer (Locd (e + Tok b))
    locdkwd' kwd tok = (Right tok <$) <$> locdkwd kwd

    wordChar :: Tokenizer Char
    wordChar = MC.satisfy isWordChar

    wordStart :: Tokenizer Char
    wordStart = MC.satisfy isWordStart

    operatorChar :: Tokenizer Char
    operatorChar = MC.satisfy isOperatorChar

    tokens :: Tokenizer [Locd (TokErr + Tok 'Unbrack)]
    tokens = many token

    word :: Tokenizer Text
    word = T.cons <$> wordStart <*> (T.pack <$> many wordChar)

    operator :: Tokenizer Text
    operator = T.pack <$> some operatorChar

    locdword :: Tokenizer (Locd Text)
    locdword = ML.lexeme silence $ locd word

    locdop :: Tokenizer (Locd Text)
    locdop = ML.lexeme silence $ locd operator

    token :: Tokenizer (Locd (TokErr + Tok 'Unbrack))
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
        pure $ Right <$> case bar of
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
        pure $ Right <$> case second of
          Just (_ :@ secondLoc) -> Lookup ASCII :@ (firstLoc <> secondLoc)
          Nothing -> Layout :@ firstLoc
      -- "[" and "[|"
      , do
        _ :@ brackLoc <- locd $ MC.string "["
        bar <- optional $ locd $ MC.string "|"
        _ <- silence
        pure $ Right <$> case bar of
          Just (_ :@ barLoc) -> ArrayBegin ASCII :@ (brackLoc <> barLoc)
          Nothing -> ListBegin :@ brackLoc
      , locdsym' "]"      ListEnd
      , locdsym' "\x2237" $ Lookup Unicode
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

      , fmap (Right . Word . Unqual Infix) <$> locdop
      , fmap (Right . Word . Unqual Postfix) <$> locdword
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
bracket srcName tokens = case MP.runParser bracketer name indented of
  Left err -> error $ concat
    [ "internal bracketing error: "
    , MP.parseErrorPretty err
    ]
  Right result -> result
  where
    indented = concat $ zipWith indentEach indents lines
    indentEach indent line = (:> indent) <$> line
    indents = locBeginCol . locdLoc . head <$> lines
    lines = groupBy ((==) `on` locBeginRow . locdLoc) tokens

    name :: String
    name = show srcName

    bracketer :: Bracketer [Locd (Tok 'Brack)]
    bracketer = concat <$> many item <* MP.eof

    item :: Bracketer [Locd (Tok 'Brack)]
    item = itemWhere $ const True

    itemWhere
      :: (Indented (Locd (Tok 'Unbrack)) -> Bool)
      -> Bracketer [Locd (Tok 'Brack)]
    itemWhere p = MP.try (MP.lookAhead (MC.satisfy p)) *> asum
      [ between (ArrayBegin ASCII) (ArrayEnd ASCII)
      , between (ArrayBegin Unicode) (ArrayEnd Unicode)
      , between (UnboxedBegin ASCII) (UnboxedEnd ASCII)
      , between (UnboxedBegin Unicode) (UnboxedEnd Unicode)
      , between BlockBegin BlockEnd
      , between GroupBegin GroupEnd
      , between ListBegin ListEnd
      , layout
      , pure <$> (fromUnbrack . indentedItem =<< MC.satisfy nonbracket)
      ]

    between :: Tok 'Unbrack -> Tok 'Unbrack -> Bracketer [Locd (Tok 'Brack)]
    between open close = do
      begin <- fromUnbrack . indentedItem =<< MC.satisfy ((== open) . locdItem . indentedItem)
      inner <- concat <$> many item
      end <- fromUnbrack . indentedItem =<< MC.satisfy ((== close) . locdItem . indentedItem)
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
      Layout -> MP.unexpected $ MP.Label ('c':|"olon not beginning valid layout block")
      ListBegin -> pure ListBegin
      ListEnd -> pure ListEnd
      Lookup enc -> pure $ Lookup enc
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
      colon@((_ :@ colonLoc) :> colonIndent) <- MC.satisfy
        $ (== Layout) . locdItem . indentedItem
      body <- some $ layoutLine colonIndent
      let
        -- Calculate the source location just past the end of the last token in 
        pastEnd toks = let
          lastLoc = locdLoc $ last $ last body
          in lastLoc
            { locBeginCol = locEndCol lastLoc
            , locEndCol = succ $ locEndCol lastLoc
            }
        endLoc = pastEnd $ concat body
        body' = concat $ (\ line -> let
          termLoc = pastEnd line
          in line ++ [Term :@ termLoc]) <$> body
      pure $ BlockBegin :@ colonLoc : body' ++ [BlockEnd :@ endLoc]

    layoutLine :: Col -> Bracketer [Locd (Tok 'Brack)]
    layoutLine colonIndent = do
      (first@(_ :@ firstLoc) :> _) <- MC.satisfy
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
  advance1 Proxy = advanceBrack
  advanceN Proxy w = foldl' (advanceBrack w)
  take1_ [] = Nothing
  take1_ (t:ts) = Just (t, ts)
  takeN_ n s
    | n <= 0 = Just ([], s)
    | null s = Nothing
    | otherwise = Just $ splitAt n s
  takeWhile_ = span

advanceBrack
  :: MP.Pos
  -> MP.SourcePos
  -> Indented (Locd (Tok 'Unbrack))
  -> MP.SourcePos
advanceBrack _tabWidth (MP.SourcePos name _row _col) (_ :@ loc :> _)
  = MP.SourcePos name
    (MP.mkPos $ rowVal $ locBeginRow loc)
    (MP.mkPos $ colVal $ locBeginCol loc)

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
  begin <- MP.getPosition
  result <- tok
  end <- MP.getPosition
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
