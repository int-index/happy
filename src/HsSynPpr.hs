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
ppr' lvlctx a = level lvlctx lvl a'
  where
    (lvl, a') = ppr a

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
    let (lvl, a') = ppr a
    in (lvl, ppr' LevelCtxUniv modname <> "." <> a')

instance Ppr HsExp where
  ppr (HsExpUnsafeString s) = (LevelUniv, text s)
  ppr (HsExpVar v) = ppr v
  ppr (HsExpCon c) = ppr c
  ppr (HsExpApp e1 e2) =
    (levelApp, sep [ppr' levelCtxAppLhs e1, ppr' levelCtxAppRhs e2])
  ppr (HsExpLam p e) =
    let l = hang ("\\" <> ppr' LevelCtxLamPat p <+> "->") tw (ppr' LevelCtxLamBody e)
    in (LevelLam, l)

instance Ppr HsTy where
  ppr (HsTyUnsafeString s) = (LevelUniv, text s)
  ppr (HsTyTyVar tv) = ppr tv
  ppr (HsTyTyCon tc) = ppr tc
  ppr (HsTyTup ts) = (LevelAtom, parens (hsep (punctuate comma (map (ppr' LevelCtxElem) ts))))
  ppr (HsTyList t) = (LevelAtom, brackets (ppr' LevelCtxElem t))
  ppr (HsTyApp t1 t2) = (levelApp, sep [ppr' levelCtxAppLhs t1, ppr' levelCtxAppRhs t2] )
  ppr (HsTyCtx t1 t2) = (levelArr, sep [ppr' levelCtxArrLhs t1 <+> "=>", ppr' levelCtxArrRhs t2])
  ppr (HsTyArr t1 t2) = (levelArr, sep [ppr' levelCtxArrLhs t1 <+> "->", ppr' levelCtxArrRhs t2])

instance Ppr HsPat where
  ppr (HsPatVar v) = ppr v
  ppr (HsPatCon c []) = ppr c
  ppr (HsPatCon c ps) = (levelApp, hsep (ppr' LevelCtxCon c : map (ppr' LevelCtxLamPat) ps))
  ppr (HsPatTup ps) = (LevelAtom, parens (hsep (punctuate comma (map (ppr' LevelCtxElem) ps))))
  ppr HsPatWild = (LevelAtom, "_")

instance Ppr [HsDec] where
  ppr ds = (LevelUniv, foldr ($+$) empty $ map (ppr' LevelCtxUniv) ds)

instance Ppr HsDec where
  ppr (HsDecType tc t) = (LevelUniv, hang ("type" <+> ppr' LevelCtxNameBind tc <+> equals) tw (ppr' LevelCtxLamBody t))
  ppr (HsDecNewtype tc tvs c t) =
    (LevelUniv, hang (hsep ("newtype" : ppr' LevelCtxNameBind tc : map (ppr' LevelCtxLamPat) tvs) <+> equals) tw
      (ppr' LevelCtxCon c <+> ppr' LevelCtxLamPat t))
  ppr (HsDecPatBind p e) = (LevelUniv, hang (ppr' LevelCtxPatBind p <+> equals) tw (ppr' LevelCtxLamBody e))
  ppr (HsDecFunBind v ps e) =
    (LevelUniv, hang (hsep (ppr' LevelCtxNameBind v : map (ppr' LevelCtxLamPat) ps) <+> equals) tw (ppr' LevelCtxLamBody e))
  ppr (HsDecTypeSig v t) =
    (LevelUniv, hang (ppr' LevelCtxNameBind v <+> "::") tw (ppr' LevelCtxLamBody t))
  ppr (HsDecInst tc ts ds) =
    (LevelUniv, hang
     ("instance" <+> hsep (ppr' LevelCtxCon tc : map (ppr' LevelCtxLamPat) ts) <+> "where") tw
     (ppr' LevelCtxUniv ds))
