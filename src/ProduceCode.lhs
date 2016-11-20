-----------------------------------------------------------------------------
The code generator.

(c) 1993-2001 Andy Gill, Simon Marlow
-----------------------------------------------------------------------------

> {-# LANGUAGE OverloadedStrings #-}
> {-# LANGUAGE PatternGuards #-}
> module ProduceCode (produceParser) where

> import Paths_happy            ( version )
> import Data.Version           ( showVersion )
> import Grammar
> import Target                 ( Target(..) )
> import GenUtils               ( mapDollarDollar, str, interleave, brack' )
> import HsSyn
> import HsSynPpr

> import Data.Maybe
> import Data.Char
> import Data.String
> import Data.List
> import Data.Monoid

> import Control.Monad      ( forM_, guard )
> import Control.Monad.ST
> import Data.Bits          ( setBit )
> import Data.Array.ST      ( STUArray )
> import Data.Array.Unboxed ( UArray )
> import Data.Array.MArray
> import Data.Array.IArray

%-----------------------------------------------------------------------------
Produce the complete output file.

> produceParser :: Grammar                      -- grammar info
>               -> ActionTable                  -- action table
>               -> GotoTable                    -- goto table
>               -> String                       -- stuff to go at the top
>               -> Maybe String                 -- module header
>               -> Maybe String                 -- module trailer
>               -> Target                       -- type of code required
>               -> Bool                         -- use coercions
>               -> Bool                         -- use ghc extensions
>               -> Bool                         -- strict parser
>               -> String

> produceParser (Grammar
>               { productions = prods
>               , non_terminals = nonterms
>               , terminals = terms
>               , types = nt_types
>               , first_nonterm = first_nonterm'
>               , eof_term = eof
>               , first_term = fst_term
>               , token_names = token_names'
>               , lexer = lexer'
>               , imported_identity = imported_identity'
>               , monad = (use_monad,monad_context,monad_tycon,monad_then,monad_return)
>               , token_specs = token_rep
>               , token_type = token_type'
>               , starts = starts'
>               , error_handler = error_handler'
>               , error_sig = error_sig'
>               , attributetype = attributetype'
>               , attributes = attributes'
>               })
>               action goto top_options module_header module_trailer
>               target coerce ghc strict
>     = prettyPrint $
>       top_opts ++
>       fmap fromString (maybeToList module_header) ++
>       -- comment goes *after* the module header, so that we
>       -- don't screw up any OPTIONS pragmas in the header.
>       [happyComment] ++
>       produceAbsSynDecl ++
>       produceTypes ++
>       produceExpListPerState ++
>       produceActionTable target ++
>       produceReductions ++
>       produceTokenConverter ++
>       produceIdentityStuff ++
>       produceMonadStuff ++
>       [fromString $ produceEntries ""] ++ -- TODO
>       [produceStrict strict] ++
>       produceAttributes attributes' attributetype' ++
>       fmap fromString (maybeToList module_trailer)
>  where
>    n_starts = length starts' :: Int
>    token' = fromString token_type' :: HsTy
>    monad_then' = fromString monad_then :: HsExp
>    monad_return' = fromString monad_return :: HsExp
>    monad_context' = fromString monad_context :: HsTy
>    monad_tycon' = fromString monad_tycon :: HsTy
>
>    nowarn_opts = decPragma "OPTIONS_GHC" "-w"
>       -- XXX Happy-generated code is full of warnings.  Some are easy to
>       -- fix, others not so easy, and others would require GHC version
>       -- #ifdefs.  For now I'm just disabling all of them.
>
>    top_opts = nowarn_opts :
>      case top_options of
>        "" -> []
>        _  -> [decPragma "OPTIONS" top_options]

%-----------------------------------------------------------------------------
Make the abstract syntax type declaration, of the form:

data HappyAbsSyn a t1 .. tn
        = HappyTerminal a
        | HappyAbsSyn1 t1
        ...
        | HappyAbsSynn tn

>    produceAbsSynDecl

If we're using coercions, we need to generate the injections etc.

        data HappyAbsSyn ti tj tk ... = HappyAbsSyn

(where ti, tj, tk are type variables for the non-terminals which don't
 have type signatures).

        happyIn<n> :: ti -> HappyAbsSyn ti tj tk ...
        happyIn<n> x = unsafeCoerce# x
        {-# INLINE happyIn<n> #-}

        happyOut<n> :: HappyAbsSyn ti tj tk ... -> tn
        happyOut<n> x = unsafeCoerce# x
        {-# INLINE happyOut<n> #-}

>     | coerce =
>       let
>         happy_item = tyApp (tyCon "HappyAbsSyn") all_tyvars'
>
>         inject n ty = [
>           decTypeSig [var (mkHappyIn n)] $
>             tyVar (type_param n ty) `tyArr` happy_item,
>           decFun (var (mkHappyIn n)) [var "x"] $
>             qvar "Happy_GHC_Exts" "unsafeCoerce#" % "x",
>           decInlinePragma (mkHappyIn n) ]
>
>         extract n ty = [
>           decTypeSig [var (mkHappyOut n)] $
>             happy_item `tyArr` tyVar (type_param n ty),
>           decFun (var (mkHappyOut n)) [var "x"] $
>             qvar "Happy_GHC_Exts" "unsafeCoerce#" % "x",
>           decInlinePragma (mkHappyOut n) ]
>       in
>         [ decNewtype (tyHead "HappyAbsSyn" all_tyvars') -- see NOTE below
>             (con "HappyAbsSyn") (tyCon "HappyAny"),
>           decCppIfElse "__GLASGOW_HASKELL__ >= 607"
>             (decType (tyHead "HappyAny" []) (qtyCon "Happy_GHC_Exts" "Any"))
>             (decType (tyHead "HappyAny" []) ("a" `tyForall` tyVar "a")) ] ++
>         concat [ inject n ty ++ extract n ty | (n,ty) <- assocs nt_types ] ++
>          -- token injector
>         [ decTypeSig ["happyInTok"] $
>             token' `tyArr` happy_item,
>           decFun "happyInTok" [var "x"] $
>             qvar "Happy_GHC_Exts" "unsafeCoerce#" % var "x",
>           decInlinePragma "happyInTok" ] ++
>           -- token extractor
>         [ decTypeSig ["happyOutTok"] $
>             happy_item `tyArr` token',
>           decFun "happyOutTok" [var "x"] $
>             qvar "Happy_GHC_Exts" "unsafeCoerce#" % var "x",
>           decInlinePragma "happyOutTok" ]

NOTE: in the coerce case we always coerce all the semantic values to
HappyAbsSyn which is declared to be a synonym for Any.  This is the
type that GHC officially knows nothing about - it's the same type used
to implement Dynamic.  (in GHC 6.6 and older, Any didn't exist, so we
use the closest approximation namely forall a . a).

It's vital that GHC doesn't know anything about this type, because it
will use any knowledge it has to optimise, and if the knowledge is
false then the optimisation may also be false.  Previously we used (()
-> ()) as the type here, but this led to bogus optimisations (see GHC
ticket #1616).

Also, note that we must use a newtype instead of just a type synonym,
because the otherwise the type arguments to the HappyAbsSyn type
constructor will lose information.  See happy/tests/bug001 for an
example where this matters.

... Otherwise, output the declaration in full...

>     | otherwise =
>       let
>         absSynCons =
>           [ conDef "HappyTerminal" [token'],
>             conDef "HappyErrorToken" [tyCon "Int"] ] ++
>           [ conDef (makeAbsSynCon n) [tyVar (type_param n ty)] |
>             (n, ty) <- assocs nt_types,
>             (nt_types_index ! n) == n ]
>       in
>         [ decData (tyHead "HappyAbsSyn" all_tyvars') absSynCons ]

>     where
>       all_tyvars' :: FromTyVar a => [a]
>       all_tyvars' = do
>         (n, Nothing) <- assocs nt_types
>         [tyVar (fromString ('t':show n))]

%-----------------------------------------------------------------------------
Type declarations of the form:

type HappyReduction a b = ....
action_0, action_1 :: Int -> HappyReduction a b
reduction_1, ...   :: HappyReduction a b

These are only generated if types for *all* rules are given (and not for array
based parsers -- types aren't as important there).

>    produceTypes
>     | target == TargetArrayBased = []

>     | all isJust (elems nt_types) =
>       let
>         actionNames = do
>           (i,_action') <- zip [ 0 :: Int .. ] (assocs action)
>           [mkActionName i]
>         actionNameType =
>           monad_context' `tyCtx`
>           intMaybeHash `tyArr`
>           happyReductionValue
>         reduceFuns = do
>           (i,_action) <-
>             zip [ n_starts :: Int .. ] (drop n_starts prods)
>           [mkReduceFun i]
>         reduceFunType =
>           monad_context' `tyCtx` happyReductionValue
>       in
>         [ happyReductionDefinition,
>           decTypeSig actionNames actionNameType,
>           decTypeSig reduceFuns reduceFunType ]

>     | otherwise = []

>       where
>         intMaybeHash :: HsTy
>         intMaybeHash
>           | ghc       = qtyCon "Happy_GHC_Exts" "Int#"
>           | otherwise = tyCon "Int"
>         tokens r =
>           case lexer' of
>             Nothing -> tyList token' `tyArr` r
>             Just _ -> r
>         happyReductionDefinition =
>           decComment $ unlines [
>             "to allow type-synonyms as our monads (likely",
>             "with explicitly-specified bind and return)",
>             "in Haskell98, it seems that with",
>             "/type M a = .../, then /(HappyReduction M)/",
>             "is not allowed.  But Happy is a",
>             "code-generator that can just substitute it.\n",
>             prettyPrint (decType (tyHead "HappyReduction" ["m"]) $ happyReduction (tyVar "m")) ]
>         happyReductionValue =
>           tyCommentBefore
>             (prettyPrint (tyCon "HappyReduction" % monad_tycon') ++ " =")
>             (happyReduction monad_tycon')
>         happyReduction m =
>           intMaybeHash `tyArr` token' `tyArr` hstate `tyArr`
>           tyList hstate `tyArr` hstk `tyArr` tokens result
>             where
>               hstk   = tyCon "HappyStk" % tyCon "HappyAbsSyn"
>               hstate = "HappyState" % token' % (hstk `tyArr` tokens result)
>               result = m % tyCon "HappyAbsSyn"

%-----------------------------------------------------------------------------
Next, the reduction functions.   Each one has the following form:

happyReduce_n_m = happyReduce n m reduction where {
   reduction (
        (HappyAbsSynX  | HappyTerminal) happy_var_1 :
        ..
        (HappyAbsSynX  | HappyTerminal) happy_var_q :
        happyRest)
         = HappyAbsSynY
                ( <<user supplied string>> ) : happyRest
        ; reduction _ _ = notHappyAtAll n m

where n is the non-terminal number, and m is the rule number.

NOTES on monad productions.  These look like

        happyReduce_275 = happyMonadReduce 0# 119# happyReduction_275
        happyReduction_275 (happyRest)
                =  happyThen (code) (\r -> happyReturn (HappyAbsSyn r))

why can't we pass the HappyAbsSyn constructor to happyMonadReduce and
save duplicating the happyThen/happyReturn in each monad production?
Because this would require happyMonadReduce to be polymorphic in the
result type of the monadic action, and since in array-based parsers
the whole thing is one recursive group, we'd need a type signature on
happyMonadReduce to get polymorphic recursion.  Sigh.

>    produceReductions = concat $
>      zipWith produceReduction
>        (drop n_starts prods) [ n_starts .. ]

>    produceReduction (nt, toks, (code,vars_used), _) i

>     | use_monad || imported_identity',
>       Just monad_reduce <- m_monad_reduce =
>       [ reduceFunImpl (var monad_reduce % expIntHash' lt),
>         decFun reductionFun
>           [patInterHappyStk tokPatterns, var "tk"] $
>           (var "happyThen" %
>              -- FIXME: this part is untested. No tests make
>              -- monad_pass_token=True
>              (if monad_pass_token
>                then (% var "tk")
>                else id) (tokLets code')) %
>           (expLam (var "r") $
>             var "happyReturn" % (this_absSynCon % var "r")) ]

>     | specReduceFun lt =
>       [ reduceFunImpl (var (mkSpecReduceFun lt)),
>         decFun reductionFun tokPatterns $
>           tokLets (this_absSynCon % code')
>       ] ++
>       if coerce || null toks || null vars_used
>         then []
>         else [
>           decFun reductionFun (replicate (length toks) patWild) $
>             var "notHappyAtAll" ]

>     | otherwise =
>       [ reduceFunImpl (var "happyReduce" % expIntHash' lt),
>         decFun reductionFun [patInterHappyStk tokPatterns] $
>           tokLets $
>             con "HappyStk" %
>             (this_absSynCon % code') %
>             var "happyRest" ]

>       where
>         code' :: HsExp
>         (code', monad_pass_token, m_monad_reduce) =
>           case code of
>             '%':'%':code1 -> (fromString code1, True, Just "happyMonad2Reduce")
>             '%':'^':code1 -> (fromString code1, True, Just "happyMonadReduce")
>             '%':code1     -> (fromString code1, False, Just "happyMonadReduce")
>             _ -> (fromString code, False, Nothing)

>         -- adjust the nonterminal number for the array-based parser
>         -- so that nonterminals start at zero.
>         adjusted_nt
>           | target == TargetArrayBased = nt - first_nonterm'
>           | otherwise                  = nt
>
>         reduceFunImpl s =
>           decFun (mkReduceFun i) [] $
>             s % expIntHash' adjusted_nt % var reductionFun
>
>         reductionFun :: HsVar
>         reductionFun = fromString ("happyReduction_" ++ show i)
>
>         patInterHappyStk :: [HsPat] -> HsPat
>         patInterHappyStk =
>           foldr (\p ps -> patCon "HappyStk" [p, ps])
>             (var "happyRest")
>
>         tokPatterns
>          | coerce = reverse (map (var . mkDummyVar) [1 .. length toks])
>          | otherwise = reverse (zipWith tokPattern [1..] toks)
>
>         tokPattern n _ | n `notElem` vars_used = patWild
>         tokPattern n t | t >= firstStartTok && t < fst_term =
>           if coerce
>             then var (mkHappyVar n)
>             else patCon (makeAbsSynCon t) [var (mkHappyVar n)]
>         tokPattern n t =
>           if coerce
>             then mkHappyTerminalVar n t
>             else patCon "HappyTerminal" [mkHappyTerminalVar n t]
>
>         tokLets code''
>            | coerce = cases code''
>            | otherwise = code''
>
>         cases :: HsExp -> HsExp
>         cases = appEndo . mconcat $ do
>           (n, t) <- zip [1..] toks
>           guard (n `elem` vars_used)
>           let
>             scrut = var (extract t) % var (mkDummyVar n)
>             pat   = tokPattern n t
>           [Endo (expCase1 scrut pat)]
>
>         extract t =
>           if t >= firstStartTok && t < fst_term
>             then mkHappyOut t
>             else var "happyOutTok"
>
>         lt = length toks

>         this_absSynCon :: HsExp
>         this_absSynCon
>           | coerce    = var (mkHappyIn nt)
>           | otherwise = con (makeAbsSynCon nt)

%-----------------------------------------------------------------------------
The token conversion function.

>    produceTokenConverter = case lexer' of
>
>       Nothing -> [
>         decFun "happyNewToken"
>           [var "action", var "sts", var "stk", patList []] $
>           eofAction (var "notHappyAtAll") % expList [],
>         let
>           defaultExp =
>             var "happyError'" % expTup [
>               con ":" % var "tk" % var "tks",
>               expList [] ]
>           caseExp =
>             expCase (var "tk") $
>               map doToken token_rep ++ [(patWild, defaultExp)]
>           letExp =
>             expLet [
>               decFun "cont" [var "i"] $
>                 doAction % var "sts" % var "stk" % var "tks" ]
>             caseExp
>         in
>           decFun "happyNewToken"
>             [ var "action", var "sts", var "stk",
>               patCon ":" [var "tk", var "tks"] ]
>             letExp,
>         decFun "happyError_"
>           [var "explist", tokPat eof, var "tk", var "tks"]
>           (var "happyError'" % expTup [var "tks", var "explist"]),
>           -- when the token is EOF, tk == _|_ (notHappyAtAll)
>           -- so we must not pass it to happyError'
>         decFun "happyError_"
>           [var "explist", patWild, var "tk", var "tks"]
>           (var "happyError'" % expTup [
>             con ":" % var "tk" % var "tks",
>             var "explist"]) ]

>       Just (lexer'',eof') ->
>         (if target == TargetHaskell && ghc
>           then [
>             decTypeSig ["happyNewToken"] $
>               ( qtyCon "Happy_GHC_Exts" "Int#" `tyArr`
>                 qtyCon "Happy_GHC_Exts" "Int#" `tyArr`
>                 tyCon "Token" `tyArr`
>                 ( tyCon "HappyState" % tyCon "Token" %
>                   ( tyVar "t" `tyArr`
>                     tyList (tyCon "Char") `tyArr`
>                     tyCon "Int" `tyArr`
>                     tyCon "ParseResult" % tyVar "a" ) ) `tyArr`
>                 tyList (
>                   tyCon "HappyState" % tyCon "Token" %
>                   ( tyVar "t" `tyArr`
>                     tyList (tyCon "Char") `tyArr`
>                     tyCon "Int" `tyArr`
>                     tyCon "ParseResult" % tyVar "a" ) ) `tyArr`
>                 tyVar "t" `tyArr`
>                 tyList (tyCon "Char") `tyArr`
>                 tyCon "Int" `tyArr`
>                 tyCon "ParseResult" % tyVar "a" ) `tyArr`
>               tyList (
>                 tyCon "HappyState" % tyCon "Token" %
>                   ( tyVar "t" `tyArr`
>                     tyList (tyCon "Char") `tyArr`
>                     tyCon "Int" `tyArr`
>                     tyCon "ParseResult" % tyVar "a" ) ) `tyArr`
>               tyVar "t" `tyArr`
>               tyList (tyCon "Char") `tyArr`
>               tyCon "Int" `tyArr`
>               tyCon "ParseResult" % tyVar "a"
>             ]
>           else []) ++
>         [ let
>             defaultExp =
>               var "happyError'" % expTup [var "tk", expList []]
>             caseExp =
>               expCase (var "tk") $
>                 [(fromString eof', eofAction (var "tk"))] ++
>                 map doToken token_rep ++
>                 [(patWild, defaultExp)]
>             letExp =
>               expLet [
>                 decFun "cont" [var "i"] $
>                   doAction % var "sts" % var "stk" ]
>               caseExp
>             lamExp = expLam (var "tk") letExp
>           in
>             decFun "happyNewToken"
>               [var "action", var "sts", var "stk"]
>               (fromString lexer'' % lamExp),
>           decFun "happyError_"
>             [var "explist", tokPat eof, var "tk"]
>             (var "happyError'" % expTup [var "tk", var "explist"]),
>             -- superfluous pattern match needed to force happyError_ to
>             -- have the correct type.
>           decFun "happyError_"
>             [var "explist", patWild, var "tk"]
>             (var "happyError'" % expTup [var "tk", var "explist"]) ]

>       where

>         eofAction :: HsExp -> HsExp
>         eofAction tk
>           | target == TargetArrayBased =
>               var "happyDoAction" %
>                 tokExp eof %
>                 tk %
>                 var "action" %
>                 var "sts" %
>                 var "stk"
>           | otherwise =
>               var "action" %
>                 tokExp eof %
>                 tokExp eof %
>                 tk %
>                 (con "HappyState" % var "action") %
>                 var "sts" %
>                 var "stk"
>
>         doAction :: HsExp
>         doAction
>           | target == TargetArrayBased =
>               var "happyDoAction" %
>                 var "i" %
>                 var "tk" %
>                 var "action"
>           | otherwise =
>               var "action" %
>                 var "i" %
>                 var "i" %
>                 var "tk" %
>                 (con "HappyState" % var "action")
>
>         doToken :: (Int, String) -> (HsPat, HsExp)
>         doToken (i,tok) =
>           (removeDollarDollar tok, var "cont" % tokExp i)

Use a variable rather than '_' to replace '$$', so we can use it on
the left hand side of '@'.

>         removeDollarDollar :: String -> HsPat
>         removeDollarDollar xs = fromString $
>           case mapDollarDollar xs of
>             Nothing -> xs
>             Just fn -> fn "happy_dollar_dollar"

>    mkHappyTerminalVar :: Int -> Int -> HsPat
>    mkHappyTerminalVar i t =
>     case tok_str_fn of
>       Nothing -> var pat
>       Just fn ->
>         -- TODO: figure out how to update mapDollarDollar
>         fromString (fn (pstr pat ""))
>     where
>         tok_str_fn = case lookup t token_rep of
>           Nothing -> Nothing
>           Just str' -> mapDollarDollar str'
>         pat = mkHappyVar i

>    tokExp :: Int -> HsExp
>    tokExp = expIntHash' . tokIndex
>
>    tokPat :: Int -> HsPat
>    tokPat = patIntHash' . tokIndex
>
>    tokIndex :: Int -> Int
>    tokIndex = case target of
>      TargetHaskell    -> id
>      TargetArrayBased ->
>        -- tokens adjusted to start at zero, see ARRAY_NOTES
>        \i -> i - n_nonterminals - n_starts - 2

%-----------------------------------------------------------------------------
Action Tables.

Here we do a bit of trickery and replace the normal default action
(failure) for each state with at least one reduction action.  For each
such state, we pick one reduction action to be the default action.
This should make the code smaller without affecting the speed.  It
changes the sematics for errors, however; errors could be detected in
a different state now (but they'll still be detected at the same point
in the token stream).

Further notes on default cases:

Default reductions are important when error recovery is considered: we
don't allow reductions whilst in error recovery, so we'd like the
parser to automatically reduce down to a state where the error token
can be shifted before entering error recovery.  This is achieved by
using default reductions wherever possible.

One case to consider is:

State 345

        con -> conid .                                      (rule 186)
        qconid -> conid .                                   (rule 212)

        error          reduce using rule 212
        '{'            reduce using rule 186
        etc.

we should make reduce_212 the default reduction here.  So the rules become:

   * if there is a production
        error -> reduce_n
     then make reduce_n the default action.
   * if there is a non-reduce action for the error token, the default action
     for this state must be "fail".
   * otherwise pick the most popular reduction in this state for the default.
   * if there are no reduce actions in this state, then the default
     action remains 'enter error recovery'.

This gives us an invariant: there won't ever be a production of the
type 'error -> reduce_n' explicitly in the grammar, which means that
whenever an unexpected token occurs, either the parser will reduce
straight back to a state where the error token can be shifted, or if
none exists, we'll get a parse error.  In theory, we won't need the
machinery to discard states in the parser...

>    produceActionTable TargetHaskell =
>      concatMap (produceStateFunction goto) (assocs action)
>
>    produceActionTable TargetArrayBased =
>      produceActionArray ++
>      [produceReduceArray] ++ [
>        decTypeSig ["happy_n_terms", "happy_n_nonterms"] (tyCon "Int"),
>        decFun "happy_n_terms" [] $ expInt n_terminals,
>        decFun "happy_n_nonterms" [] $ expInt n_nonterminals ]
>
>    produceExpListPerState =
>      produceExpListArray ++ [
>        decNoInlinePragma "happyExpListPerState",
>        decFunWhere "happyExpListPerState" [var "st"]
>          (var "token_strs_expected")
>          [
>            decFun "token_strs" [] $
>              expList (map expStr (elems token_names')),
>            decFun "bit_start" [] $
>              var "*" % var "st" % expInt nr_tokens,
>            decFun "bit_end" [] $
>              var "*" % expPlusOne (var "st") % expInt nr_tokens,
>            decFun "read_bit" [] $
>              var "readArrayBit" % var "happyExpList",
>            decFun "bits" [] $
>              var "map" % var "read_bit" %
>                expEnumFromTo
>                  (var "bit_start")
>                  (var "-" % var "bit_end" % expInt (1 :: Int)),
>            decFun "bits_indexed" [] $
>              var "zip" % var "bits" %
>                expEnumFromTo
>                  (expInt (0 :: Int))
>                  (expInt (nr_tokens - 1)),
>            decFun "token_strs_expected" [] $
>              var "concatMap" % var "f" % var "bits_indexed",
>            decFun "f" [patTup [con "False", patWild]] $ expList [],
>            decFun "f" [patTup [con "True", var "nr"]] $
>              expList [var "!!" % var "token_strs" % var "nr"]
>          ]
>        ]
>       where
>         (first_token, last_token) = bounds token_names'
>         nr_tokens = last_token - first_token + 1
>         expPlusOne e = var "+" % e % expInt (1 :: Int)
>
>    produceStateFunction goto' (state, acts) =
>      concatMap produceActions assocs_acts ++
>      concatMap produceGotos (assocs gotos) ++
>      [produceDefaultAction]
>
>       where
>         gotos = goto' ! state
>
>         callHappyExpListPerState =
>           var "happyExpListPerState" % expInt state
>
>         produceActions (_, LR'Fail{-'-}) = []
>         produceActions (t, action'@(LR'Reduce{-'-} _ _))
>            | action' == default_act = []
>            | otherwise = [producePossiblyFailingAction t action']
>         produceActions (t, action') =
>           [producePossiblyFailingAction t action']
>
>         producePossiblyFailingAction t action' =
>           actionFunction t $ mkAction action' (expList [])
>
>         produceGotos (_, NoGoto) = []
>         produceGotos (t, Goto i) = [
>           actionFunction t $
>             var "happyGoto" % var (mkActionName i) ]
>
>         actionFunction t =
>           decFun (mkActionName state) [patIntHash' t]
>
>         produceDefaultAction
>           | ghc =
>               decFun (mkActionName state) [var "x"] $
>                 var "happyTcHack" % var "x" %
>                   mkAction default_act callHappyExpListPerState
>           | otherwise =
>               decFun (mkActionName state) [patWild] $
>                 mkAction default_act callHappyExpListPerState
>
>         default_act = getDefault assocs_acts
>
>         assocs_acts = assocs acts

action array indexed by (terminal * last_state) + state

>    produceConstArray name upper_bound values
>      | ghc =
>        [ decTypeSig [name] (tyCon "HappyAddr"),
>          decFun name [] $ con "HappyA#" % expHexChars values ]
>      | otherwise =
>        [ decTypeSig [name] $
>            qtyCon "Happy_Data_Array" "Array" %
>              tyCon "Int" %
>              tyCon "Int",
>          decFun name [] $
>            qcon "Happy_Data_Array" "listArray" %
>              expTup [expInt (0 :: Int), expInt upper_bound] %
>              expList (map expInt values) ]
>
>    produceActionArray =
>      produceConstArray "happyActOffsets" n_states act_offs ++
>      produceConstArray "happyGotoOffsets" n_states goto_offs ++
>      produceConstArray "happyDefActions" n_states defaults ++
>      produceConstArray "happyCheck" table_size check ++
>      produceConstArray "happyTable" table_size table

>    produceExpListArray =
>      produceConstArray "happyExpList" table_size explist

>    (_, last_state) = bounds action
>    n_states = last_state + 1
>    n_terminals = length terms
>    n_nonterminals = length nonterms - n_starts -- lose %starts
>
>    (act_offs,goto_offs,table,defaults,check,explist)
>       = mkTables action goto first_nonterm' fst_term
>               n_terminals n_nonterminals n_starts (bounds token_names')
>
>    table_size = length table - 1
>
>    produceReduceArray =
>      decFun "happyReduceArr" [] $
>        qvar "Happy_Data_Array" "array" %
>          expTup [
>            -- omit the %start reductions
>            expInt n_starts,
>            expInt n_rules ] %
>          expList (map reduceArrElem [n_starts..n_rules])

>    n_rules = length prods - 1 :: Int

>    expIntHash'
>      | ghc       = expIntHash
>      | otherwise = expInt
>
>    patIntHash'
>      | ghc       = patIntHash
>      | otherwise = patInt

This lets examples like:

        data HappyAbsSyn t1
                = HappyTerminal ( HaskToken )
                | HappyAbsSyn1 (  HaskExp  )
                | HappyAbsSyn2 (  HaskExp  )
                | HappyAbsSyn3 t1

*share* the defintion for ( HaskExp )

        data HappyAbsSyn t1
                = HappyTerminal ( HaskToken )
                | HappyAbsSyn1 (  HaskExp  )
                | HappyAbsSyn3 t1

... cuting down on the work that the type checker has to do.

Note, this *could* introduce lack of polymophism,
for types that have alphas in them. Maybe we should
outlaw them inside { }

>    nt_types_index :: Array Int Int
>    nt_types_index = array (bounds nt_types)
>                       [ (a, fn a b) | (a, b) <- assocs nt_types ]
>     where
>       fn n Nothing = n
>       fn _ (Just a) = case lookup a assoc_list of
>                         Just v -> v
>                         Nothing -> error ("cant find an item in list")
>       assoc_list = [ (b,a) | (a, Just b) <- assocs nt_types ]

>    makeAbsSynCon = mkAbsSynCon nt_types_index


>    produceIdentityStuff | use_monad = []
>     | imported_identity' = [
>         decType (tyHead "HappyIdentity" []) (tyCon "Identity"),
>         decFun "happyIdentity" [] (con "Identity"),
>         decFun "happyRunIdentity" [] (var "runIdentity") ]
>     | otherwise = [
>         decNewtype (tyHead "HappyIdentity" ["a"])
>           (con "HappyIdentity") (tyVar "a"),
>         decFun "happyIdentity" [] (con "HappyIdentity"),
>         decFun "happyRunIdentity"
>           [patCon "HappyIdentity" [var "a"]] (var "a"),
>         decInst (tyCon "Functor") [tyCon "HappyIdentity"] [
>           decFun "fmap"
>             [var "f", patCon "HappyIdentity" [var "a"]]
>             (con "HappyIdentity" % (var "f" % var "a")) ],
>         decInst (tyCon "Applicative") [tyCon "HappyIdentity"] [
>           decFun "pure" [] (con "HappyIdentity"),
>           decFun "<*>" [] (var "ap") ],
>         decInst (tyCon "Monad") [tyCon "HappyIdentity"] [
>           decFun "return" [] (var "pure"),
>           decFun ">>="
>             [patCon "HappyIdentity" [var "p"], var "q"]
>             (var "q" % var "p") ] ]

MonadStuff:

  - with no %monad or %lexer:

        happyThen    :: () => HappyIdentity a -> (a -> HappyIdentity b) -> HappyIdentity b
        happyReturn  :: () => a -> HappyIdentity a
        happyThen1   m k tks = happyThen m (\a -> k a tks)
        happyReturn1 = \a tks -> happyReturn a

  - with %monad:

        happyThen    :: CONTEXT => P a -> (a -> P b) -> P b
        happyReturn  :: CONTEXT => a -> P a
        happyThen1   m k tks = happyThen m (\a -> k a tks)
        happyReturn1 = \a tks -> happyReturn a

  - with %monad & %lexer:

        happyThen    :: CONTEXT => P a -> (a -> P b) -> P b
        happyReturn  :: CONTEXT => a -> P a
        happyThen1   = happyThen
        happyReturn1 = happyReturn


>    produceMonadStuff = [
>      decTypeSig ["happyThen"] (
>        monad_context' `tyCtx`
>        monad_tycon' % tyVar "a" `tyArr`
>        (tyVar "a" `tyArr` monad_tycon' % tyVar "b") `tyArr`
>        monad_tycon' % tyVar "b" ),
>      decFun "happyThen" [] monad_then',
>      decTypeSig ["happyReturn"] (
>         monad_context' `tyCtx`
>         tyVar "a" `tyArr`
>         monad_tycon' % tyVar "a" ),
>      decFun "happyReturn" [] monad_return' ] ++
>      case lexer' of
>        Nothing -> [
>          decFun "happyThen1" [var "m", var "k", var "tks"] (
>            monad_then' %
>            var "m" %
>            (var "a" `expLam` var "k" % var "a" % var "tks") ),
>          decTypeSig ["happyReturn1"] (
>            monad_context' `tyCtx`
>            tyVar "a" `tyArr`
>            tyVar "b" `tyArr`
>            monad_tycon' % tyVar "a" ),
>          decFun "happyReturn1" []
>            (var "a" `expLam` var "tks" `expLam`
>              monad_return' % var "a"),
>          decTypeSig ["happyError'"] (
>            monad_context' `tyCtx`
>            tyTup [tyList token', tyList (tyVar "String")] `tyArr`
>            monad_tycon' % tyVar "a" ),
>          decFun "happyError'" [] (
>            (if use_monad then id else (\x -> var "." % con "HappyIdentity" % x))
>            errorHandler ) ]
>        _ -> [
>          decFun "happyThen1" [] (var "happyThen"),
>          decTypeSig ["happyReturn1"] (
>            monad_context' `tyCtx`
>            tyVar "a" `tyArr`
>            monad_tycon' % tyVar "a" ),
>          decFun "happyReturn1" [] (var "happyReturn"),
>          decTypeSig ["happyError'"] (
>            monad_context' `tyCtx`
>            tyTup [token', tyList (tyVar "String")] `tyArr`
>            monad_tycon' % tyVar "a" ),
>          decFun "happyError'" [var "tk"] (
>            (if use_monad then id else (con "HappyIdentity" %))
>            (errorHandler % var "tk") ) ]

An error handler specified with %error is passed the current token
when used with %lexer, but happyError (the old way but kept for
compatibility) is not passed the current token. Also, the %errorhandlertype
directive determins the API of the provided function.

>    errorHandler =
>      case error_handler' of
>        Just h  -> case error_sig' of
>          ErrorHandlerTypeExpList -> fromString h
>          ErrorHandlerTypeDefault ->
>            expLam (patTup [var "tokens", patWild]) $
>              fromString h % var "tokens"
>        Nothing -> case lexer' of
>          Nothing ->
>            expLam (patTup [var "tokens", patWild]) $
>              var "happyError" % var "tokens"
>          Just _  ->
>            expLam (patTup [var "tokens", var "explist"]) $
>              var "happyError"

>    reduceArrElem n = expTup [expInt n, var (mkReduceFun n)]

-----------------------------------------------------------------------------
-- Produce the parser entry and exit points

>    produceEntries
>       = interleave "\n\n" (map produceEntry (zip starts' [0..]))
>       . if null attributes' then id else produceAttrEntries starts'

>    produceEntry :: ((String, t0, Int, t1), Int) -> String -> String
>    produceEntry ((name, _start_nonterm, accept_nonterm, _partial), no)
>       = (if null attributes' then str name else str "do_" . str name)
>       . maybe_tks
>       . str " = "
>       . str unmonad
>       . str "happySomeParser where\n"
>       . str "  happySomeParser = happyThen (happyParse "
>       . case target of
>            TargetHaskell -> str "action_" . shows no
>            TargetArrayBased
>                | ghc       -> shows no . str "#"
>                | otherwise -> shows no
>       . maybe_tks
>       . str ") "
>       . brack' (if coerce
>                    then str "\\x -> happyReturn (happyOut"
>                       . shows accept_nonterm . str " x)"
>                    else str "\\x -> case x of {HappyAbsSyn"
>                       . shows (nt_types_index ! accept_nonterm)
>                       . str " z -> happyReturn z; _other -> notHappyAtAll }"
>                )
>     where
>       maybe_tks | isNothing lexer' = str " tks"
>                 | otherwise = id
>       unmonad | use_monad = ""
>                 | otherwise = "happyRunIdentity "

>    produceAttrEntries starts''
>       = interleave "\n\n" (map f starts'')
>     where
>       f = case (use_monad,lexer') of
>             (True,Just _)  -> \(name,_,_,_) -> monadAndLexerAE name
>             (True,Nothing) -> \(name,_,_,_) -> monadAE name
>             (False,Just _) -> error "attribute grammars not supported for non-monadic parsers with %lexer"
>             (False,Nothing)-> \(name,_,_,_) -> regularAE name
>
>       defaultAttr = fst (head attributes')
>
>       monadAndLexerAE name
>         = str name . str " = "
>         . str "do { "
>         . str "f <- do_" . str name . str "; "
>         . str "let { (conds,attrs) = f happyEmptyAttrs } in do { "
>         . str "sequence_ conds; "
>         . str "return (". str defaultAttr . str " attrs) }}"
>       monadAE name
>         = str name . str " toks = "
>         . str "do { "
>         . str "f <- do_" . str name . str " toks; "
>         . str "let { (conds,attrs) = f happyEmptyAttrs } in do { "
>         . str "sequence_ conds; "
>         . str "return (". str defaultAttr . str " attrs) }}"
>       regularAE name
>         = str name . str " toks = "
>         . str "let { "
>         . str "f = do_" . str name . str " toks; "
>         . str "(conds,attrs) = f happyEmptyAttrs; "
>         . str "x = foldr seq attrs conds; "
>         . str "} in (". str defaultAttr . str " x)"

----------------------------------------------------------------------------
-- Produce attributes declaration for attribute grammars

> produceAttributes :: [(String, String)] -> String -> [HsDec]
> produceAttributes []    _             = []
> produceAttributes attrs attributeType = [
>   decData attrHeader
>     [conDefRec "HappyAttributes" $ map formatAttribute attrs],
>   decFun "happyEmptyAttrs" [] $
>     expRec "HappyAttributes" (map attrError attrs) ]
>   where
>     formatAttribute (ident, typ) = (ident', typ')
>       where
>         ident' = fromString ident :: HsVar
>         typ' = fromString typ :: HsTy
>     attrError (ident, _) = (ident', errExp)
>       where
>         ident' = fromString ident :: HsVar
>         errExp = var "error" % expStr errMsg
>         errMsg = "invalid reference to attribute '" ++ ident ++ "'"
>     attrHeader =
>       case attributeType of
>         [] -> tyHead "HappyAttributes" []
>         _  -> fromString attributeType


-----------------------------------------------------------------------------
-- Strict or non-strict parser

> produceStrict :: Bool -> HsDec
> produceStrict strict =
>   decFun "happySeq" [] $
>     if strict then var "happyDoSeq" else var "happyDontSeq"

-----------------------------------------------------------------------------
Replace all the $n variables with happy_vars, and return a list of all the
vars used in this piece of code.

> actionVal :: LRAction -> Int
> actionVal (LR'Shift  state _) = state + 1
> actionVal (LR'Reduce rule _)  = -(rule + 1)
> actionVal LR'Accept           = -1
> actionVal (LR'Multiple _ a)   = actionVal a
> actionVal LR'Fail             = 0
> actionVal LR'MustFail         = 0

> mkAction :: LRAction -> HsExp -> HsExp
> mkAction act failArg = case act of
>   (LR'Shift i _)    -> var "happyShift" % var (mkActionName i)
>   LR'Accept         -> var "happyAccept"
>   LR'Fail           -> var "happyFail" % failArg
>   LR'MustFail       -> var "happyFail" % failArg
>   (LR'Reduce i _)   -> var (mkReduceFun i)
>   (LR'Multiple _ a) -> mkAction a failArg

> mkActionName :: Int -> HsVar
> mkActionName i = fromString ("action_" ++ show i)

See notes under "Action Tables" above for some subtleties in this function.

> getDefault :: [(Name, LRAction)] -> LRAction
> getDefault actions =
>   -- pick out the action for the error token, if any
>   case [ act | (e, act) <- actions, e == errorTok ] of
>
>       -- use error reduction as the default action, if there is one.
>       act@(LR'Reduce _ _) : _                 -> act
>       act@(LR'Multiple _ (LR'Reduce _ _)) : _ -> act
>
>       -- if the error token is shifted or otherwise, don't generate
>       --  a default action.  This is *important*!
>       (act : _) | act /= LR'Fail -> LR'Fail
>
>       -- no error actions, pick a reduce to be the default.
>       _      -> case reduces of
>                     [] -> LR'Fail
>                     (act:_) -> act    -- pick the first one we see for now
>
>   where reduces
>           =  [ act | (_,act@(LR'Reduce _ _)) <- actions ]
>           ++ [ act | (_,(LR'Multiple _ act@(LR'Reduce _ _))) <- actions ]

-----------------------------------------------------------------------------
-- Generate packed parsing tables.

-- happyActOff ! state
--     Offset within happyTable of actions for state

-- happyGotoOff ! state
--     Offset within happyTable of gotos for state

-- happyTable
--      Combined action/goto table

-- happyDefAction ! state
--      Default action for state

-- happyCheck
--      Indicates whether we should use the default action for state


-- the table is laid out such that the action for a given state & token
-- can be found by:
--
--        off    = happyActOff ! state
--        off_i  = off + token
--        check  | off_i => 0 = (happyCheck ! off_i) == token
--               | otherwise  = False
--        action | check      = happyTable ! off_i
--               | otherwise  = happyDefAaction ! off_i


-- figure out the default action for each state.  This will leave some
-- states with no *real* actions left.

-- for each state with one or more real actions, sort states by
-- width/spread of tokens with real actions, then by number of
-- elements with actions, so we get the widest/densest states
-- first. (I guess the rationale here is that we can use the
-- thin/sparse states to fill in the holes later, and also we
-- have to do less searching for the more complicated cases).

-- try to pair up states with identical sets of real actions.

-- try to fit the actions into the check table, using the ordering
-- from above.


> mkTables
>        :: ActionTable -> GotoTable -> Name -> Int -> Int -> Int -> Int -> (Int, Int) ->
>        ([Int]         -- happyActOffsets
>        ,[Int]         -- happyGotoOffsets
>        ,[Int]         -- happyTable
>        ,[Int]         -- happyDefAction
>        ,[Int]         -- happyCheck
>        ,[Int]         -- happyExpList
>        )
>
> mkTables action goto first_nonterm' fst_term
>               n_terminals n_nonterminals n_starts
>               token_names_bound
>
>  = ( elems act_offs,
>      elems goto_offs,
>      take max_off (elems table),
>      def_actions,
>      take max_off (elems check),
>      elems explist
>   )
>  where
>
>        (table,check,act_offs,goto_offs,explist,max_off)
>                = runST (genTables (length actions)
>                         max_token token_names_bound
>                         sorted_actions explist_actions)
>
>        -- the maximum token number used in the parser
>        max_token = max n_terminals (n_starts+n_nonterminals) - 1
>
>        def_actions = map (\(_,_,def,_,_,_) -> def) actions
>
>        actions :: [TableEntry]
>        actions =
>                [ (ActionEntry,
>                   state,
>                   actionVal default_act,
>                   if null acts'' then 0
>                        else fst (last acts'') - fst (head acts''),
>                   length acts'',
>                   acts'')
>                | (state, acts) <- assocs action,
>                  let (err:_dummy:vec) = assocs acts
>                      vec' = drop (n_starts+n_nonterminals) vec
>                      acts' = filter (notFail) (err:vec')
>                      default_act = getDefault acts'
>                      acts'' = mkActVals acts' default_act
>                ]
>
>        explist_actions :: [(Int, [Int])]
>        explist_actions = [ (state, concat $ map f $ assocs acts)
>                          | (state, acts) <- assocs action ]
>                          where
>                            f (t, LR'Shift _ _ ) = [t - fst token_names_bound]
>                            f (_, _) = []
>
>        -- adjust terminals by -(fst_term+1), so they start at 1 (error is 0).
>        --  (see ARRAY_NOTES)
>        adjust token | token == errorTok = 0
>                     | otherwise         = token - fst_term + 1
>
>        mkActVals assocs' default_act =
>                [ (adjust token, actionVal act)
>                | (token, act) <- assocs'
>                , act /= default_act ]
>
>        gotos :: [TableEntry]
>        gotos = [ (GotoEntry,
>                   state, 0,
>                   if null goto_vals then 0
>                        else fst (last goto_vals) - fst (head goto_vals),
>                   length goto_vals,
>                   goto_vals
>                  )
>                | (state, goto_arr) <- assocs goto,
>                let goto_vals = mkGotoVals (assocs goto_arr)
>                ]
>
>        -- adjust nonterminals by -first_nonterm', so they start at zero
>        --  (see ARRAY_NOTES)
>        mkGotoVals assocs' =
>                [ (token - first_nonterm', i) | (token, Goto i) <- assocs' ]
>
>        sorted_actions = reverse (sortBy cmp_state (actions++gotos))
>        cmp_state (_,_,_,width1,tally1,_) (_,_,_,width2,tally2,_)
>                | width1 < width2  = LT
>                | width1 == width2 = compare tally1 tally2
>                | otherwise = GT

> data ActionOrGoto = ActionEntry | GotoEntry
> type TableEntry = (ActionOrGoto,
>                       Int{-stateno-},
>                       Int{-default-},
>                       Int{-width-},
>                       Int{-tally-},
>                       [(Int,Int)])

> genTables
>        :: Int                         -- number of actions
>        -> Int                         -- maximum token no.
>        -> (Int, Int)                  -- token names bounds
>        -> [TableEntry]                -- entries for the table
>        -> [(Int, [Int])]              -- expected tokens lists
>        -> ST s (UArray Int Int,       -- table
>                 UArray Int Int,       -- check
>                 UArray Int Int,       -- action offsets
>                 UArray Int Int,       -- goto offsets
>                 UArray Int Int,       -- expected tokens list
>                 Int                   -- highest offset in table
>           )
>
> genTables n_actions max_token token_names_bound entries explist = do
>
>   table      <- newArray (0, mAX_TABLE_SIZE) 0
>   check      <- newArray (0, mAX_TABLE_SIZE) (-1)
>   act_offs   <- newArray (0, n_actions) 0
>   goto_offs  <- newArray (0, n_actions) 0
>   off_arr    <- newArray (-max_token, mAX_TABLE_SIZE) 0
>   exp_array  <- newArray (0, (n_actions * n_token_names + 15) `div` 16) 0
>
>   max_off <- genTables' table check act_offs goto_offs off_arr exp_array entries
>                       explist max_token n_token_names
>
>   table'     <- freeze table
>   check'     <- freeze check
>   act_offs'  <- freeze act_offs
>   goto_offs' <- freeze goto_offs
>   exp_array' <- freeze exp_array
>   return (table',check',act_offs',goto_offs',exp_array',max_off+1)

>   where
>        n_states = n_actions - 1
>        mAX_TABLE_SIZE = n_states * (max_token + 1)
>        (first_token, last') = token_names_bound
>        n_token_names = last' - first_token + 1


> genTables'
>        :: STUArray s Int Int          -- table
>        -> STUArray s Int Int          -- check
>        -> STUArray s Int Int          -- action offsets
>        -> STUArray s Int Int          -- goto offsets
>        -> STUArray s Int Int          -- offset array
>        -> STUArray s Int Int          -- expected token list
>        -> [TableEntry]                -- entries for the table
>        -> [(Int, [Int])]              -- expected tokens lists
>        -> Int                         -- maximum token no.
>        -> Int                         -- number of token names
>        -> ST s Int                    -- highest offset in table
>
> genTables' table check act_offs goto_offs off_arr exp_array entries
>            explist max_token n_token_names
>       = fill_exp_array >> fit_all entries 0 1
>   where
>
>        fit_all [] max_off _ = return max_off
>        fit_all (s:ss) max_off fst_zero = do
>          (off, new_max_off, new_fst_zero) <- fit s max_off fst_zero
>          ss' <- same_states s ss off
>          writeArray off_arr off 1
>          fit_all ss' new_max_off new_fst_zero
>
>        fill_exp_array =
>          forM_ explist $ \(state, tokens) ->
>            forM_ tokens $ \token -> do
>              let bit_nr = state * n_token_names + token
>              let word_nr = bit_nr `div` 16
>              let word_offset = bit_nr `mod` 16
>              x <- readArray exp_array word_nr
>              writeArray exp_array word_nr (setBit x word_offset)
>
>        -- try to merge identical states.  We only try the next state(s)
>        -- in the list, but the list is kind-of sorted so we shouldn't
>        -- miss too many.
>        same_states _ [] _ = return []
>        same_states s@(_,_,_,_,_,acts) ss@((e,no,_,_,_,acts'):ss') off
>          | acts == acts' = do writeArray (which_off e) no off
>                               same_states s ss' off
>          | otherwise = return ss
>
>        which_off ActionEntry = act_offs
>        which_off GotoEntry   = goto_offs
>
>        -- fit a vector into the table.  Return the offset of the vector,
>        -- the maximum offset used in the table, and the offset of the first
>        -- entry in the table (used to speed up the lookups a bit).
>        fit (_,_,_,_,_,[]) max_off fst_zero = return (0,max_off,fst_zero)
>
>        fit (act_or_goto, state_no, _deflt, _, _, state@((t,_):_))
>           max_off fst_zero = do
>                -- start at offset 1 in the table: all the empty states
>                -- (states with just a default reduction) are mapped to
>                -- offset zero.
>          off <- findFreeOffset (-t+fst_zero) check off_arr state
>          let new_max_off | furthest_right > max_off = furthest_right
>                          | otherwise                = max_off
>              furthest_right = off + max_token
>
>          -- trace ("fit: state " ++ show state_no ++ ", off " ++ show off ++ ", elems " ++ show state) $ do
>
>          writeArray (which_off act_or_goto) state_no off
>          addState off table check state
>          new_fst_zero <- findFstFreeSlot check fst_zero
>          return (off, new_max_off, new_fst_zero)

When looking for a free offest in the table, we use the 'check' table
rather than the main table.  The check table starts off with (-1) in
every slot, because that's the only thing that doesn't overlap with
any tokens (non-terminals start at 0, terminals start at 1).

Because we use 0 for LR'MustFail as well as LR'Fail, we can't check
for free offsets in the main table because we can't tell whether a
slot is free or not.

> -- Find a valid offset in the table for this state.
> findFreeOffset :: Int -> STUArray s Int Int -> STUArray s Int Int -> [(Int, Int)] -> ST s Int
> findFreeOffset off table off_arr state = do
>     -- offset 0 isn't allowed
>   if off == 0 then try_next else do
>
>     -- don't use an offset we've used before
>   b <- readArray off_arr off
>   if b /= 0 then try_next else do
>
>     -- check whether the actions for this state fit in the table
>   ok <- fits off state table
>   if not ok then try_next else return off
>  where
>       try_next = findFreeOffset (off+1) table off_arr state


> fits :: Int -> [(Int,Int)] -> STUArray s Int Int -> ST s Bool
> fits _   []           _     = return True
> fits off ((t,_):rest) table = do
>   i <- readArray table (off+t)
>   if i /= -1 then return False
>              else fits off rest table

> addState :: Int -> STUArray s Int Int -> STUArray s Int Int -> [(Int, Int)]
>          -> ST s ()
> addState _   _     _     [] = return ()
> addState off table check ((t,val):state) = do
>    writeArray table (off+t) val
>    writeArray check (off+t) t
>    addState off table check state

> notFail :: (Int, LRAction) -> Bool
> notFail (_, LR'Fail) = False
> notFail _           = True

> findFstFreeSlot :: STUArray s Int Int -> Int -> ST s Int
> findFstFreeSlot table n = do
>        i <- readArray table n
>        if i == -1 then return n
>                   else findFstFreeSlot table (n+1)

-----------------------------------------------------------------------------
-- Misc.

> happyComment :: HsDec
> happyComment = decComment $
>   "parser produced by Happy Version " ++ showVersion version

> mkAbsSynCon :: Array Int Int -> Int -> HsCon
> mkAbsSynCon fx t = fromString $ "HappyAbsSyn" ++ show (fx ! t)

> mkHappyVar, mkReduceFun, mkSpecReduceFun, mkDummyVar :: Int -> HsVar
> mkHappyVar n = fromString ("happy_var_" ++ show n)
> mkReduceFun n = fromString ("happyReduce_" ++ show n)
> mkSpecReduceFun n = fromString ("happySpecReduce_" ++ show n)
> mkDummyVar n = fromString ("happy_x_" ++ show n)

> mkHappyIn, mkHappyOut :: Int -> HsVar
> mkHappyIn n = fromString ("happyIn" ++ show n)
> mkHappyOut n = fromString ("happyOut" ++ show n)

> type_param :: Int -> Maybe String -> HsTyVar
> type_param n Nothing = fromString ('t' : show n)
> type_param _ (Just ty) = fromString ty

> specReduceFun :: Int -> Bool
> specReduceFun = (<= 3)

-----------------------------------------------------------------------------
-- Convert an integer to a 16-bit number encoded in \xNN\xNN format suitable
-- for placing in a string.

> expHexChars :: [Int] -> HsExp
> expHexChars = expStrHash . concatMap hexChar'
>   where
>     hexChar' :: Int -> String
>     hexChar' i | i < 0 = hexChar' (i + 65536)
>     hexChar' i = map chr [i `mod` 256, i `div` 256]
