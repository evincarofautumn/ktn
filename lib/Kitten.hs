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

import Data.Ratio ((%))
import Data.Text (Text)
import Data.Vector (Vector)
import GHC.Types (Type)
import qualified Text.Megaparsec as Megaparsec

-- | The radix of an numeric literal.
data Base
  = Bin
  | Oct
  | Dec
  | Hex
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

-- | The contents of a character literal.
data CharLit :: Type where
  CharLit :: !(Esc + Char) -> CharLit
  deriving (Show)

-- | A column in a source location.
newtype Col = Col Int
  deriving (Show)

-- | The encoding of a token with both ASCII and Unicode spellings.
data Enc :: Type where
  ASCII :: Enc
  Unicode :: Enc
  deriving (Show)

-- | An error message.
newtype ErrMsg = ErrMsg Text
  deriving (Show)

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

  deriving (Show)

-- | The lexical fixity of a word: 'Infix' for operators, 'Postfix' otherwise.
data Fixity :: Type where
  Postfix :: Fixity
  Infix :: Fixity
  deriving (Show)

-- | The precision of a floating-point number.
data FloatBits :: Type where
  F32 :: FloatBits
  F64 :: FloatBits
  deriving (Show)

-- | A floating-point literal of the form @FloatLit a b c bits@ denoting the
-- floating-point number @a * 10 ^ (c - b)@ with precision of @bits@.
data FloatLit :: Type where
  FloatLit ::
    { floatLitSig :: !Integer
    , floatLitFrac :: !Int
    , floatLitExp :: !Int
    , floatLitBits :: !FloatBits
    } -> FloatLit
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
  deriving (Show)

-- | An integer literal.
data IntLit :: Type where
  IntLit ::
    { intLitVal :: !Integer
    , intLitBase :: !Base
    , intLitBits :: !IntBits
    } -> IntLit
  deriving (Show)

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

-- | The contents of a paragraph literal.
data ParaLit :: Type where
  ParaLit :: !(Vector (Vector (Esc + Text))) -> ParaLit
  deriving (Show)

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

-- | The contents of a text literal.
data TextLit :: Type where
  TextLit :: !(Vector (Esc + Text)) -> TextLit
  deriving (Show)

-- | A token, indexed by a 'Brack'eting that indicates whether it has been
-- 'bracket'ed.
data Tok :: Brack -> Type where

  -- Keywords

  -- | @about@ keyword.
  About :: Tok b
  -- | @as@ keyword.
  As :: Tok b
  -- | @case@ keyword.
  Case :: Tok b
  -- | @define@ keyword.
  Define :: Tok b
  -- | @do@ keyword.
  Do :: Tok b
  -- | @elif@ keyword.
  Elif :: Tok b
  -- | @else@ keyword.
  Else :: Tok b
  -- | @export@ keyword.
  Export :: Tok b
  -- | @if@ keyword.
  If :: Tok b
  -- | @import@ keyword.
  Import :: Tok b
  -- | @instance@ keyword.
  Instance :: Tok b
  -- | @intrinsic@ keyword.
  Intrinsic :: Tok b
  -- | @jump@ keyword.
  Jump :: Tok b
  -- | @match@ keyword.
  Match :: Tok b
  -- | @loop@ keyword.
  Loop :: Tok b
  -- | @permission@ keyword.
  Permission :: Tok b
  -- | @return@ keyword.
  Return :: Tok b
  -- | @synonym@ keyword.
  Synonym :: Tok b
  -- | @trait@ keyword.
  Trait :: Tok b
  -- | @type@ keyword.
  Type :: Tok b
  -- | @vocab@ keyword.
  Vocab :: Tok b
  -- | @with@ keyword.
  With :: Tok b

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
  Arrow :: Tok b
  -- | Beginning of block: U+007B LEFT CURLY BRACKET.
  BlockBegin :: Tok b
  -- | End of block: U+007D RIGHT CURLY BRACKET.
  BlockEnd :: Tok b
  -- | To-do placeholder or stack kind sigil: U+002E U+002E U+002E PERIOD or
  -- U+2026 HORIZONTAL ELLIPSIS.
  Ellipsis :: Tok b
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
  -- | Reference to term: U+005C BACKSLASH.
  Ref :: Tok b
  -- | Sequence delimiter: U+002C COMMA.
  Seq :: Tok b
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

  -- | Operator name.
  Op :: !Unqual -> Tok b
  -- | Word name.
  Word :: Tok b

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

--------------------------------------------------------------------------------

floatLitVal :: Fractional a => FloatLit -> a
floatLitVal (FloatLit sig frac ex _bits)
  = fromRational $ (fromIntegral sig :: Rational) * shift
  where
    delta = ex - frac
    shift
      | delta < 0 = 1 % 10 ^ negate delta
      | otherwise = 10 ^ delta
