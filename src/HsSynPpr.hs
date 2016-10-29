{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
module HsSynPpr
  ( Ppr(..)
  , Level(..)
  , pstr
  ) where

import Data.Char
import Data.Function
import HsSyn
import Text.PrettyPrint

pstr :: Ppr a => a -> String -> String
pstr = (++) . render . ppr' LevelCtxUniv

vsep :: [Doc] -> Doc
vsep = foldr ($+$) empty

tw :: Int
tw = 2

isSymbolicIdent :: String -> Bool
isSymbolicIdent (c:_) = isPunctuation c || isSymbol c
isSymbolicIdent _ = False

data Fixity = Leftfix Int | Rightfix Int | Nonfix Int

precedence :: Fixity -> Int
precedence (Leftfix n) = n
precedence (Rightfix n) = n
precedence (Nonfix n) = n

data Level =
  LevelAtom |
  LevelSymbol (Maybe Fixity) |
  LevelUniv |
  LevelLam |
  LevelInfix Fixity

levelArr :: Level
levelArr = LevelInfix (Rightfix 0)

levelApp :: Level
levelApp = LevelInfix (Leftfix 10)

data LevelCtx =
  LevelCtxUniv |
  LevelCtxNameBind |
  LevelCtxPatBind |
  LevelCtxLamPat |
  LevelCtxLamBody |
  LevelCtxElem |
  LevelCtxCon |
  LevelCtxInfixLhs Fixity |
  LevelCtxInfixRhs Fixity

levelCtxAppLhs :: LevelCtx
levelCtxAppLhs = LevelCtxInfixLhs (Leftfix 10)

levelCtxAppRhs :: LevelCtx
levelCtxAppRhs = LevelCtxInfixRhs (Leftfix 10)

levelCtxArrLhs :: LevelCtx
levelCtxArrLhs = LevelCtxInfixLhs (Rightfix 0)

levelCtxArrRhs :: LevelCtx
levelCtxArrRhs = LevelCtxInfixRhs (Rightfix 0)

level :: LevelCtx -> Level -> Doc -> Doc
level LevelCtxUniv _ = id
level _ LevelAtom = id
level _ (LevelSymbol _) = parens
level (LevelCtxInfixRhs (Rightfix m)) (LevelInfix (Rightfix n)) | n >= m = id
level (LevelCtxInfixLhs (Leftfix m)) (LevelInfix (Leftfix n)) | n >= m = id
level (LevelCtxInfixRhs ctxfx) (LevelInfix fx) | on (>) precedence fx ctxfx = id
level (LevelCtxInfixLhs ctxfx) (LevelInfix fx) | on (>) precedence fx ctxfx = id
level LevelCtxLamBody LevelLam = id
level LevelCtxLamBody (LevelInfix _) = id
level _ _ = parens

class Ppr a where
  ppr :: a -> (Level, Doc)

ppr' :: Ppr a => LevelCtx -> a -> Doc
ppr' lvlctx a = level lvlctx lvl aDoc
  where
    (lvl, aDoc) = ppr a

pprIdent :: String -> (Level, Doc)
pprIdent s = (lvl, text s)
  where
    lvl = if isSymbolicIdent s then LevelSymbol Nothing else LevelAtom

instance Ppr HsVar where
  ppr (HsVar s) = pprIdent s

instance Ppr HsCon where
  ppr (HsCon s) = pprIdent s

instance Ppr HsTyVar where
  ppr (HsTyVar s) = pprIdent s

instance Ppr HsTyCon where
  ppr (HsTyCon s) = pprIdent s

instance Ppr HsModuleName where
  ppr (HsModuleName s) = (LevelAtom, text s)

instance Ppr a => Ppr (HsQual a) where
  ppr (HsQual Nothing a) = ppr a
  ppr (HsQual (Just modname) a) =
    let (lvl, aDoc) = ppr a
    in (lvl, ppr' LevelCtxUniv modname <> "." <> aDoc)

instance Ppr HsExp where
  ppr (HsExpUnsafeString s) = (LevelUniv, text s)
  ppr (HsExpVar v) = ppr v
  ppr (HsExpCon c) = ppr c
  ppr (HsExpApp eLhs eRhs) =
    let eLhsDoc = ppr' levelCtxAppLhs eLhs; eRhsDoc = ppr' levelCtxAppRhs eRhs
    in (levelApp, sep [eLhsDoc, eRhsDoc])
  ppr (HsExpLam p e) =
    let pDoc = ppr' LevelCtxLamPat p; eDoc = ppr' LevelCtxLamBody e
    in (LevelLam, hang ("\\" <> pDoc <+> "->") tw eDoc)

pprTuple :: [Doc] -> Doc
pprTuple = parens . hsep . punctuate comma 

instance Ppr HsTy where
  ppr (HsTyUnsafeString s) = (LevelUniv, text s)
  ppr (HsTyTyVar tv) = ppr tv
  ppr (HsTyTyCon tc) = ppr tc
  ppr (HsTyTup ts) =
    let tsDocs = map (ppr' LevelCtxElem) ts
    in (LevelAtom, pprTuple tsDocs)
  ppr (HsTyList t) =
    let tl = brackets (ppr' LevelCtxElem t)
    in (LevelAtom, tl)
  ppr (HsTyApp tLhs tRhs) =
    let tLhsDoc = ppr' levelCtxAppLhs tLhs; tRhsDoc = ppr' levelCtxAppRhs tRhs
    in (levelApp, sep [tLhsDoc, tRhsDoc])
  ppr (HsTyCtx tLhs tRhs) =
    let tLhsDoc = ppr' levelCtxArrLhs tLhs; tRhsDoc = ppr' levelCtxArrRhs tRhs
    in (levelArr, sep [tLhsDoc <+> "=>", tRhsDoc])
  ppr (HsTyArr tLhs tRhs) =
    let tLhsDoc = ppr' levelCtxArrLhs tLhs; tRhsDoc = ppr' levelCtxArrRhs tRhs
    in (levelArr, sep [tLhsDoc <+> "->", tRhsDoc])
  ppr (HsTyForall tv t) =
    let tvDoc = ppr' LevelCtxLamPat tv; tDoc = ppr' LevelCtxLamBody t
    in (LevelLam, "forall" <+> tvDoc <+> "." <+> tDoc)

instance Ppr HsPat where
  ppr (HsPatVar v) = ppr v
  ppr (HsPatCon c []) = ppr c
  ppr (HsPatCon c ps) =
    let cDoc = ppr' LevelCtxCon c; psDocs = map (ppr' LevelCtxLamPat) ps
    in (levelApp, hsep (cDoc : psDocs))
  ppr (HsPatTup ps) =
    let psDocs = map (ppr' LevelCtxElem) ps
    in (LevelAtom, pprTuple psDocs)
  ppr HsPatWild = (LevelAtom, "_")

instance Ppr [HsDec] where
  ppr ds =
    let dsDocs = map (ppr' LevelCtxUniv) ds
    in (LevelUniv, vsep dsDocs)

instance Ppr HsDec where
  ppr (HsDecPragma name content) =
    let nameDoc = text (map toUpper name); contentDoc = text content
    in (LevelUniv, "{-#" <+> nameDoc <+> contentDoc <+> "#-}" )
  ppr (HsDecInlinePragma (HsVar v)) =
    ppr (HsDecPragma "INLINE" v)
  ppr (HsDecCppIfElse condS thenD elseD) =
    (LevelUniv, cppIfElseDoc)
    where
      cppIfElseDoc = vsep
        [ "#if" <+> text condS,
          ppr' LevelCtxUniv thenD,
          "#else",
          ppr' LevelCtxUniv elseD,
          "#endif" ]
  ppr (HsDecType tc t) =
    let tcDoc = ppr' LevelCtxNameBind tc; tDoc = ppr' LevelCtxLamBody t
    in (LevelUniv, hang ("type" <+> tcDoc <+> equals) tw tDoc)
  ppr (HsDecNewtype tc tvs c t) =
    (LevelUniv, hang (headerDoc <+> equals) tw cdDoc)
    where
      tcDoc = ppr' LevelCtxNameBind tc
      tvsDocs = map (ppr' LevelCtxLamPat) tvs
      headerDoc = hsep ("newtype" : tcDoc : tvsDocs)
      cDoc = ppr' LevelCtxCon c
      tDoc = ppr' LevelCtxLamPat t
      cdDoc = cDoc <+> tDoc
  ppr (HsDecData tc tvs cds) =
    (LevelUniv, hang (headerDoc <+> equals) tw cdsDoc)
    where
      tcDoc = ppr' LevelCtxNameBind tc
      tvsDocs = map (ppr' LevelCtxLamPat) tvs
      headerDoc = hsep ("data" : tcDoc : tvsDocs)
      cdsDoc = sep . punctuate " |" $ do
        (c, ts) <- cds
        let
          cDoc = ppr' LevelCtxCon c;
          tsDocs = map (ppr' LevelCtxLamPat) ts
        [cDoc <+> hsep tsDocs]
  ppr (HsDecPatBind p e) =
    let pDoc = ppr' LevelCtxPatBind p; eDoc = ppr' LevelCtxLamBody e
    in (LevelUniv, hang (pDoc <+> equals) tw eDoc)
  ppr (HsDecFunBind v ps e) =
    (LevelUniv, hang (headerDoc <+> equals) tw eDoc)
    where
      vDoc = ppr' LevelCtxNameBind v
      psDocs = map (ppr' LevelCtxLamPat) ps
      headerDoc = hsep (vDoc : psDocs)
      eDoc = ppr' LevelCtxLamBody e
  ppr (HsDecTypeSig v t) =
    let vDoc = ppr' LevelCtxNameBind v; tDoc = ppr' LevelCtxLamBody t
    in (LevelUniv, hang (vDoc <+> "::") tw tDoc)
  ppr (HsDecInst tc ts ds) =
    (LevelUniv, instDoc)
    where
      tcDoc = ppr' LevelCtxCon tc
      tsDocs = map (ppr' LevelCtxLamPat) ts
      dsDoc = ppr' LevelCtxUniv ds
      headerDoc = hsep (tcDoc : tsDocs)
      instDoc = hang ("instance" <+> headerDoc <+> "where") tw dsDoc
