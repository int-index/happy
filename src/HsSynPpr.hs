{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
-- TODO: levels are actually only applicable to expressions. Separate them
-- from normal ppr?
module HsSynPpr
  ( Ppr(..)
  , Level(..)
  , prettyPrint
  ) where

import Data.Char
import Data.Function
import HsSyn
import Text.PrettyPrint
import Numeric (showHex)

prettyPrint :: Ppr a => a -> String
prettyPrint = render . ppr' LevelCtxUniv

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

-- TODO: Write a function Exp -> Level instead of returning levels
-- from ppr
data Level =
  LevelAtom |
  LevelSymbol (Maybe Fixity) |
  LevelUniv |
  LevelLam |
  LevelInfix Fixity |
  LevelComment

levelArr :: Level
levelArr = LevelInfix (Rightfix 0)

levelApp :: Level
levelApp = LevelInfix (Leftfix 10)

-- TODO: instead of LevelCtx reified as a data type, represent it
-- as a function 'Level -> Doc -> Doc' (same as 'level' applied)
data LevelCtx =
  LevelCtxUniv |
  LevelCtxNameBind |
  LevelCtxPatBind |
  LevelCtxLamPat |
  LevelCtxLamBody |
  LevelCtxElem |
  LevelCtxCon |
  LevelCtxInfixLhs Fixity |
  LevelCtxInfixRhs Fixity |
  LevelCtxCommentBefore |
  LevelCtxCommentAfter |
  LevelCtxCaseScrut |
  LevelCtxCasePat |
  LevelCtxCaseExp

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

pprCommentOpen :: HsComment -> (Level, Doc)
pprCommentOpen (HsComment ls) = case ls of
  []  -> (LevelAtom, empty)
  [l] -> (LevelUniv, "--" <+> text l)
  _   -> (LevelAtom, "{-" $+$ vsep (map text ls) $+$ "-}")

pprCommentClosed :: HsComment -> Doc
pprCommentClosed (HsComment ls) = case ls of
  [] -> empty
  _  -> "{-" <+> vsep (map text ls) <+> "-}"


pprIntHash :: HsHashLit -> Integer -> (Level, Doc)
pprIntHash h n = (lvl, nDoc)
  where
    lvl = if n < 0 then LevelUniv else LevelAtom
    hDoc = case h of
      HsHashLit True -> "#"
      HsHashLit False -> empty
    nDoc = text (show n) <> hDoc

pprExp :: HsExp -> (Level, Doc)

pprExp (HsExpUnsafeString s) = (LevelUniv, text s)

pprExp (HsExpVar v) = ppr v

pprExp (HsExpCon c) = ppr c

pprExp (HsExpApp eLhs eRhs) = (levelApp, appDoc)
  where
    appDoc = hang eLhsDoc tw eRhsDoc
    eLhsDoc = ppr' levelCtxAppLhs eLhs
    eRhsDoc = ppr' levelCtxAppRhs eRhs

pprExp (HsExpLam p e) = (LevelLam, lamDoc)
  where
    lamDoc = hang ("\\" <> pDoc <+> "->") tw eDoc
    pDoc = ppr' LevelCtxLamPat p
    eDoc = ppr' LevelCtxLamBody e

pprExp (HsExpTup es) = (LevelAtom, pprTuple esDocs)
  where
    esDocs = map (ppr' LevelCtxElem) es

pprExp (HsExpList es) = (LevelAtom, esDoc)
  where
    esDocs = map (ppr' LevelCtxElem) es
    esDoc = pprList esDocs

pprExp (HsExpRec c fs) = (LevelAtom, erDoc)
  where
    cDoc = ppr' LevelCtxUniv c
    fsDocs = do
      (name, e) <- fs
      let
        nameDoc = ppr' LevelCtxUniv name
        eDoc = ppr' LevelCtxUniv e
      [hang (nameDoc <+> equals) tw eDoc]
    erDoc = cDoc <+> pprRec fsDocs

pprExp (HsExpCase e bs) = (LevelUniv, caseDoc)
  where
    caseDoc = hang headerDoc tw bsDoc
    headerDoc = "case" <+> eDoc <+> "of"
    eDoc = ppr' LevelCtxCaseScrut e
    bsDoc
      | null bsDocs = "{}"
      | otherwise   = vsep bsDocs
    bsDocs = do
      (p, be) <- bs
      let
        pDoc = ppr' LevelCtxCasePat p
        beDoc = ppr' LevelCtxCaseExp be
      [hang (pDoc <+> "->") tw beDoc]

pprExp (HsExpLet ds e) = (LevelUniv, elDoc)
  where
    eDoc = ppr' LevelCtxUniv e
    dsDoc = ppr' LevelCtxUniv ds
    elDoc = sep [
      "let",
      nest tw dsDoc,
      "in",
      nest tw eDoc ]

pprExp (HsExpDo ss) = (LevelLam, edDoc)
  where
    ssDocs = map (ppr' LevelCtxUniv) ss
    edDoc = hang "do" tw (vsep ssDocs)

pprExp (HsExpEnumFromTo eFrom eTo) = (LevelAtom, eeftDoc)
  where
    eFromDoc = ppr' LevelCtxElem eFrom
    eToDoc = ppr' LevelCtxElem eTo
    eeftDoc = brackets $ eFromDoc <+> ".." <+> eToDoc

pprExp (HsExpInt h n) = pprIntHash h n

pprExp (HsExpStr (HsHashLit False) s) = (LevelAtom, sDoc)
  where
    sDoc = text (show s)

pprExp (HsExpStr (HsHashLit True) s) = (LevelAtom, sDoc <> "#")
  where
    sDoc
      | all isPrint s = text (show s)
      | otherwise = text (showHexStr s)

instance Ppr HsStmt where
  ppr (HsStmtBind p e) = (LevelUniv, sbDoc)
    where
      pDoc = ppr' LevelCtxUniv p
      eDoc = ppr' LevelCtxUniv e
      sbDoc = hang (pDoc <+> "<-") tw eDoc
  ppr (HsStmtLet ds) = (LevelUniv, slDoc)
    where
      dsDocs = map (ppr' LevelCtxUniv) ds
      slDoc = hang "let" tw (vsep dsDocs)
  ppr (HsStmtExp e) = ppr e

instance Ppr HsExp where
  ppr = pprExp

-- TODO: split into multiline literals when too long
showHexStr :: String -> String
showHexStr s = '\"' : foldr (.) id (map showHexChar s) "\""
  where
    showHexChar c = ("\\x" ++) . showHex (ord c)

pprTuple :: [Doc] -> Doc
pprTuple = parens . hsep . punctuate comma

pprList :: [Doc] -> Doc
pprList = brackets . fsep . punctuate comma

pprRec :: [Doc] -> Doc
pprRec = braces . vsep . punctuate comma

instance Ppr HsTy where
  ppr (HsTyUnsafeString s) = (LevelUniv, text s)
  ppr (HsTyCommentBefore com t) = (LevelComment, tcomDoc)
    where
      tcomDoc = sep [comDoc, tDoc]
      tDoc = ppr' LevelCtxCommentBefore t
      comDoc = pprCommentClosed com
  ppr (HsTyCommentAfter com t) = (LevelComment, tcomDoc)
    where
      tcomDoc = sep [tDoc, comDoc]
      tDoc = ppr' LevelCtxCommentAfter t
      comDoc = pprCommentClosed com
  ppr (HsTyTyVar tv) = ppr tv
  ppr (HsTyTyCon tc) = ppr tc
  ppr (HsTyTup ts) =
    (LevelAtom, pprTuple tsDocs)
    where
      tsDocs = map (ppr' LevelCtxElem) ts
  ppr (HsTyList t) =
    (LevelAtom, tl)
    where
      tl = brackets (ppr' LevelCtxElem t)
  ppr (HsTyApp tLhs tRhs) = (levelApp, taDoc)
    where
      taDoc = hang tLhsDoc tw tRhsDoc
      tLhsDoc = ppr' levelCtxAppLhs tLhs
      tRhsDoc = ppr' levelCtxAppRhs tRhs
  ppr (HsTyCtx tLhs tRhs) =
    (levelArr, tCtxDoc)
    where
      tLhsDoc = ppr' levelCtxArrLhs tLhs
      tRhsDoc = ppr' levelCtxArrRhs tRhs
      tCtxDoc = sep [tLhsDoc <+> "=>", tRhsDoc]
  ppr (HsTyArr tLhs tRhs) =
    (levelArr, tArrDoc)
    where
      tLhsDoc = ppr' levelCtxArrLhs tLhs
      tRhsDoc = ppr' levelCtxArrRhs tRhs
      tArrDoc = sep [tLhsDoc <+> "->", tRhsDoc]
  ppr (HsTyForall tv t) =
    (LevelLam, tfDoc)
    where
      tvDoc = ppr' LevelCtxLamPat tv
      tDoc = ppr' LevelCtxLamBody t
      tfDoc = "forall" <+> tvDoc <+> "." <+> tDoc

instance Ppr HsPat where
  ppr (HsPatUnsafeString s) = (LevelUniv, text s)
  ppr (HsPatVar v) = ppr v
  ppr (HsPatCon c []) = ppr c
  ppr (HsPatCon c ps) =
    (levelApp, pcDoc)
    where
      cDoc = ppr' LevelCtxCon c
      psDocs = map (ppr' LevelCtxLamPat) ps
      pcDoc = hsep (cDoc : psDocs)
  ppr (HsPatTup ps) = (LevelAtom, psDoc)
    where
      psDocs = map (ppr' LevelCtxElem) ps
      psDoc = pprTuple psDocs
  ppr (HsPatList ps) = (LevelAtom, psDoc)
    where
      psDocs = map (ppr' LevelCtxElem) ps
      psDoc = pprList psDocs
  ppr (HsPatInt h n) = pprIntHash h n
  ppr HsPatWild = (LevelAtom, "_")

instance Ppr [HsDec] where
  ppr ds =
    let dsDocs = map (ppr' LevelCtxUniv) ds
    in (LevelUniv, vsep dsDocs)

instance Ppr HsTyHead where
  ppr (HsTyHeadUnsafeString s) = (LevelUniv, text s)
  ppr (HsTyHead tc tvs) =
    (LevelUniv, thDoc)
    where
      thDoc = hsep $
        ppr' LevelCtxNameBind tc :
        map (ppr' LevelCtxLamPat) tvs

instance Ppr HsDec where
  ppr (HsDecUnsafeString s) = (LevelUniv, text s)
  ppr (HsDecComment com) = pprCommentOpen com
  ppr (HsDecPragma name content) =
    (LevelUniv, dpDoc)
    where
      nameDoc = text (map toUpper name)
      contentDoc = text content
      dpDoc = "{-#" <+> nameDoc <+> contentDoc <+> "#-}"
  ppr (HsDecInlinePragma (HsVar v)) =
    ppr (HsDecPragma "INLINE" v)
  ppr (HsDecNoInlinePragma (HsVar v)) =
    ppr (HsDecPragma "NOINLINE" v)
  ppr (HsDecCppIfElse condS thenD elseD) =
    (LevelUniv, cppIfElseDoc)
    where
      cppIfElseDoc = vsep
        [ "#if" <+> text condS,
          ppr' LevelCtxUniv thenD,
          "#else",
          ppr' LevelCtxUniv elseD,
          "#endif" ]
  ppr (HsDecType th t) =
    (LevelUniv, hang (headerDoc <+> equals) tw tDoc)
    where
      thDoc = ppr' LevelCtxUniv th
      tDoc = ppr' LevelCtxLamBody t
      headerDoc = "type" <+> thDoc
  ppr (HsDecNewtype th c t) =
    (LevelUniv, hang (headerDoc <+> equals) tw cdDoc)
    where
      thDoc = ppr' LevelCtxUniv th
      headerDoc = "newtype" <+> thDoc
      cDoc = ppr' LevelCtxCon c
      tDoc = ppr' LevelCtxLamPat t
      cdDoc = cDoc <+> tDoc
  ppr (HsDecData th cds) =
    (LevelUniv, hang (headerDoc <+> equals) tw cdsDoc)
    where
      thDoc = ppr' LevelCtxUniv th
      headerDoc = "data" <+> thDoc
      cdsDoc = sep . punctuate " |" $ do
        cd <- cds
        return $ case cd of
          HsConDef c ts ->
            let
              cDoc = ppr' LevelCtxCon c
              tsDocs = map (ppr' LevelCtxLamPat) ts
            in
              cDoc <+> hsep tsDocs
          HsConDefRec c fs ->
            let
              cDoc = ppr' LevelCtxCon c
              fsDoc = pprRec $ do
                (name, ty) <- fs
                let
                  nameDoc = ppr' LevelCtxUniv name
                  tyDoc = ppr' LevelCtxUniv ty
                [hang (nameDoc <+> "::") tw tyDoc]
            in
              cDoc <+> fsDoc
  ppr (HsDecPatBind p e) =
    (LevelUniv, pbDoc)
    where
      pDoc = ppr' LevelCtxPatBind p
      eDoc = ppr' LevelCtxLamBody e
      pbDoc = hang (pDoc <+> equals) tw eDoc
  ppr (HsDecFunBind v ps e ds) =
    (LevelUniv, if null ds then dfbDoc else dfbWhereDoc)
    where
      vDoc = ppr' LevelCtxNameBind v
      psDocs = map (ppr' LevelCtxLamPat) ps
      headerDoc = hsep (vDoc : psDocs)
      eDoc = ppr' LevelCtxLamBody e
      dsDoc = ppr' LevelCtxUniv ds
      dfbDoc = hang (headerDoc <+> equals) tw eDoc
      dfbWhereDoc =
        hang dfbDoc tw $
        hang "where" tw dsDoc
  ppr (HsDecTypeSig [] _) = (LevelUniv, empty)
  ppr (HsDecTypeSig vs t) =
    (LevelUniv, hang (headerDoc <+> "::") tw tDoc)
    where
      (vDoc:vsDocs) = map (ppr' LevelCtxNameBind) vs
      tDoc = ppr' LevelCtxLamBody t
      headerDoc
        | null vsDocs = vDoc
        | otherwise   = hang (vDoc <> ",") tw $
            fsep (punctuate "," vsDocs)
  ppr (HsDecInst tc ts ds) =
    (LevelUniv, instDoc)
    where
      tcDoc = ppr' LevelCtxCon tc
      tsDocs = map (ppr' LevelCtxLamPat) ts
      dsDoc = ppr' LevelCtxUniv ds
      headerDoc = hsep (tcDoc : tsDocs)
      instDoc = hang ("instance" <+> headerDoc <+> "where") tw dsDoc
