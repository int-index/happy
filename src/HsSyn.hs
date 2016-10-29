{-# LANGUAGE OverloadedStrings #-}
module HsSyn
  ( HsVar(..)
  , HsCon(..)
  , HsTyVar(..)
  , HsTyCon(..)
  , HsModuleName(..)
  , HsQual(..)
  , HsExp(..)
  , expLam
  , expApp
  , HsTy(..)
  , tyCtx
  , tyArr
  , tyForall
  , tyTup
  , tyList
  , tyApp
  , HsPat(..)
  , patCon
  , patTup
  , patWild
  , HsDec(..)
  , decPragma
  , decInlinePragma
  , decCppIfElse
  , decType
  , decNewtype
  , decData
  , decVal
  , decFun
  , decTypeSig
  , decInst
  ---
  , FromTyCon(..)
  , FromQTyCon(..)
  , FromCon(..)
  , FromQCon(..)
  , FromVar(..)
  , FromQVar(..)
  , FromTyVar(..)
  , FromApp(..)
  ) where

import Data.Char
import Data.String
import Data.List (foldl')

newtype HsVar = HsVar String

instance IsString HsVar where
  fromString = HsVar

newtype HsCon = HsCon String

instance IsString HsCon where
  fromString = HsCon

newtype HsTyVar = HsTyVar String

instance IsString HsTyVar where
  fromString = HsTyVar

newtype HsTyCon = HsTyCon String

instance IsString HsTyCon where
  fromString = HsTyCon

newtype HsModuleName = HsModuleName String

instance IsString HsModuleName where
  fromString = HsModuleName

data HsQual a = HsQual (Maybe HsModuleName) a

data HsExp =
  HsExpUnsafeString String |
  HsExpVar (HsQual HsVar) |
  HsExpCon (HsQual HsCon) |
  HsExpApp HsExp HsExp |
  HsExpLam HsPat HsExp

instance IsString HsExp where
  fromString s@(c:_) | all isAlpha s =
    if isUpper c then con (fromString s) else var (fromString s)
  fromString s = HsExpUnsafeString s

expLam :: HsPat -> HsExp -> HsExp
expLam = HsExpLam

infixr 2 `expLam`

expApp :: HsExp -> [HsExp] -> HsExp
expApp = foldl' (%)

data HsTy =
  HsTyUnsafeString String |
  HsTyTyVar HsTyVar |
  HsTyTyCon (HsQual HsTyCon) |
  HsTyTup [HsTy] |
  HsTyList HsTy |
  HsTyApp HsTy HsTy |
  HsTyCtx HsTy HsTy |
  HsTyArr HsTy HsTy |
  HsTyForall HsTyVar HsTy

instance IsString HsTy where
  fromString "()" = HsTyTup []
  fromString s@(c:_) | all isAlpha s =
    if isUpper c then tyCon (fromString s) else tyVar (fromString s)
  fromString s = HsTyUnsafeString s

tyCtx :: HsTy -> HsTy -> HsTy
tyCtx (HsTyTup []) t = t
tyCtx t1 t2 = HsTyCtx t1 t2

infixr 2 `tyCtx`

tyArr :: HsTy -> HsTy -> HsTy
tyArr = HsTyArr

infixr 2 `tyArr`

tyForall :: HsTyVar -> HsTy -> HsTy
tyForall = HsTyForall

infixr 2 `tyForall`

tyTup :: [HsTy] -> HsTy
tyTup = HsTyTup

tyList :: HsTy -> HsTy
tyList = HsTyList

tyApp :: HsTy -> [HsTy] -> HsTy
tyApp = foldl' (%)

data HsPat =
  HsPatVar HsVar |
  HsPatCon HsCon [HsPat] |
  HsPatTup [HsPat] |
  HsPatWild

patCon :: HsCon -> [HsPat] -> HsPat
patCon = HsPatCon

patTup :: [HsPat] -> HsPat
patTup = HsPatTup

patWild :: HsPat
patWild = HsPatWild

data HsDec =
  HsDecPragma String String |
  HsDecInlinePragma HsVar |
  HsDecCppIfElse String HsDec HsDec |
  HsDecType HsTyCon HsTy |
  HsDecNewtype HsTyCon [HsTyVar] HsCon HsTy |
  HsDecData HsTyCon [HsTyVar] [(HsCon, [HsTy])] |
  HsDecPatBind HsPat HsExp |
  HsDecFunBind HsVar [HsPat] HsExp |
  HsDecTypeSig HsVar HsTy |
  HsDecInst HsTyCon [HsTy] [HsDec]

decPragma :: String -> String -> HsDec
decPragma = HsDecPragma

decInlinePragma :: HsVar -> HsDec
decInlinePragma = HsDecInlinePragma

decCppIfElse :: String -> HsDec -> HsDec -> HsDec
decCppIfElse = HsDecCppIfElse

decType :: HsTyCon -> HsTy -> HsDec
decType = HsDecType

decNewtype :: HsTyCon -> [HsTyVar] -> HsCon -> HsTy -> HsDec
decNewtype = HsDecNewtype

decData :: HsTyCon -> [HsTyVar] -> [(HsCon, [HsTy])] -> HsDec
decData = HsDecData

decVal :: HsPat -> HsExp -> HsDec
decVal = HsDecPatBind

decFun :: HsVar -> [HsPat] -> HsExp -> HsDec
decFun = HsDecFunBind

decTypeSig :: HsVar -> HsTy -> HsDec
decTypeSig = HsDecTypeSig

decInst :: HsTyCon -> [HsTy] -> [HsDec] -> HsDec
decInst = HsDecInst

------------------------------------------------------------------------------

class FromTyCon a where
  tyCon :: HsTyCon -> a

instance FromTyCon HsTyCon where
  tyCon = id

instance FromTyCon a => FromTyCon (HsQual a) where
  tyCon s = HsQual Nothing (tyCon s)

instance FromTyCon HsTy where
  tyCon s = HsTyTyCon (tyCon s)


class FromQTyCon a where
  qtyCon :: HsModuleName -> HsTyCon -> a

instance FromTyCon a => FromQTyCon (HsQual a) where
  qtyCon modname tc = HsQual (Just modname) (tyCon tc)

instance FromQTyCon HsTy where
  qtyCon modname tc = HsTyTyCon (qtyCon modname tc)


class FromCon a where
  con :: HsCon -> a

instance FromCon HsCon where
  con = id

instance FromCon a => FromCon (HsQual a) where
  con s = HsQual Nothing (con s)

instance FromCon HsExp where
  con s = HsExpCon (con s)

instance FromCon HsPat where
  con s = patCon s []


class FromQCon a where
  qcon :: HsModuleName -> HsCon -> a

instance FromCon a => FromQCon (HsQual a) where
  qcon modname c = HsQual (Just modname) (con c)

instance FromQCon HsExp where
  qcon modname c = HsExpCon (qcon modname c)


class FromVar a where
  var :: HsVar -> a

instance FromVar HsVar where
  var = id

instance FromVar a => FromVar (HsQual a) where
  var s = HsQual Nothing (var s)

instance FromVar HsExp where
  var s = HsExpVar (var s)

instance FromVar HsPat where
  var s = HsPatVar (var s)


class FromQVar a where
  qvar :: HsModuleName -> HsVar -> a

instance FromVar a => FromQVar (HsQual a) where
  qvar modname v = HsQual (Just modname) (var v)

instance FromQVar HsExp where
  qvar modname v = HsExpVar (qvar modname v)


class FromTyVar a where
  tyVar :: HsTyVar -> a

instance FromTyVar HsTyVar where
  tyVar = id

instance FromTyVar a => FromTyVar (HsQual a) where
  tyVar s = HsQual Nothing (tyVar s)

instance FromTyVar HsTy where
  tyVar s = HsTyTyVar (tyVar s)


class FromApp a where
  (%) :: a -> a -> a

infixl 3 %

instance FromApp HsExp where
  (%) = HsExpApp

instance FromApp HsTy where
  (%) = HsTyApp