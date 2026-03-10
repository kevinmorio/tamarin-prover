-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Portability : portable
--
-- Parsing Signatures
------------------------------------------------------------------------------

module Theory.Text.Parser.Signature (
    heuristic
    , builtins
    , options
    , functions
    , equations
    , liftedAddPredicate
    , preddeclaration
    , goalRanking
    , diffbuiltins
    , export
)
where

import Term.Maude.Signature
import           Prelude
import qualified Data.ByteString.Char8      as BC
-- import           Data.Monoid                hiding (Last)
import qualified Data.Set                   as S
import           Data.Maybe                 (fromMaybe)
--import           Data.Char
--import qualified Data.Map                   as M
import           Control.Applicative        hiding (empty, many, optional)
import           Control.Monad
import qualified Control.Monad.Catch        as Catch
import           Text.Parsec                hiding ((<|>))

import           Term.Substitution
import           Term.SubtermRule
import           Theory
import           Theory.Text.Parser.Token
import Theory.Text.Parser.Fact
import Theory.Text.Parser.Term
import Theory.Text.Parser.Formula
import Theory.Text.Parser.Exceptions
import Debug.Trace (traceM)

import Data.Label.Total
import Data.Label.Mono (Lens)
import Theory.Sapic
import qualified Data.Functor

data FunctionAttribute
  = FunctionPrivate
  | FunctionConstructor
  | FunctionDestructor
  | FunctionData
  deriving (Eq, Show)


 -- Describes the mapping between Maude Signatures and the builtin Name
builtinsDiffNames :: [(String,
                       MaudeSig)]
builtinsDiffNames = [
  ("diffie-hellman", dhMaudeSig),
  ("bilinear-pairing", bpMaudeSig),
  ("multiset", msetMaudeSig),
  ("xor", xorMaudeSig),
  ("symmetric-encryption", symEncMaudeSig),
  ("asymmetric-encryption", asymEncMaudeSig),
  ("signing", signatureMaudeSig),
  ("dest-pairing", pairDestMaudeSig),  
  ("dest-symmetric-encryption", symEncDestMaudeSig),
  ("dest-asymmetric-encryption", asymEncDestMaudeSig),
  ("dest-signing", signatureDestMaudeSig),  
  ("revealing-signing", revealSignatureMaudeSig),
  ("hashing", hashMaudeSig),
  ("natural-numbers", natMaudeSig)
              ]

-- | Describes the mapping between a builtin name, its potential Maude Signatures
-- and its potential option
builtinsNames :: [([Char], Maybe MaudeSig, Maybe (Lens Total Option Bool))]
builtinsNames =
  [
  ("locations-report",  Just locationReportMaudeSig, Just transReport),
  ("reliable-channel",  Nothing, Just transReliable)
  ]
  ++ map (\(x,y) -> (x, Just y, Nothing)) builtinsDiffNames

-- | Builtin signatures.
builtins :: OpenTheory -> Parser OpenTheory
builtins thy0 =do
            _  <- symbol "builtins"
            _  <- colon
            l <- commaSep1 builtinTheory -- l is list of lenses to set options to true with
                                         -- builtinTheory modifies signature in state.
            return $ foldl setOption' thy0 l
  where
    setName thy name = modify thyItems (++ [TranslationItem (SignatureBuiltin name)]) thy
    setOption' thy (Nothing, name)  = setName thy name
    setOption' thy (Just l, name) = setOption l (setName thy name)
    -- Check for conflicts between builtin functions and user defined functions, and fail with a helpful error message if any are found.
    -- Otherwise, add the builtin signature to the state and add the reserved function names to the state.
    extendSig (name, Just msig, opt) = do
        _ <- symbol name
        st <- getState
        let builtinFuncs = S.toList $ stFunSyms msig
        let macroSyms    = S.toList $ macroNames (sig st)
        let macroFuncs   = S.fromList $ map (BC.unpack . fst) macroSyms
        let currFuncs    = S.toList $ stFunSyms (sig st)

        let functionConflicts = [ (BC.unpack fname, builtinArity, userArity)
                                | (fname, builtinArity) <- builtinFuncs
                                , (fname', userArity)   <- currFuncs
                                , fname == fname'
                                , userArity /= builtinArity
                                ]

        let macroConflicts = [ (BC.unpack fname, builtinArity, macroArity)
                      | (fname, builtinArity) <- builtinFuncs
                      , BC.unpack fname `S.member` macroFuncs
                      , Just macroArity <- [lookup fname macroSyms]
                      , macroArity /= builtinArity
                      ]

        unless (null functionConflicts || name == "dest-pairing") $ do
            fail $ "Builtin '" ++ name ++ "' conflicts with existing function(s) (same name, different arity or function options): " ++ 
                  show [fname | (fname, _, _) <- functionConflicts] ++ ". Please remove these function definitions or use different names."

        unless (null macroConflicts) $ do
            fail $ "Builtin '" ++ name ++ "' conflicts with existing macro '" ++ show [fname | (fname, _, _) <- macroConflicts] ++ "'"
        
        modifyStateSig (`mappend` msig)
        modifyState (\st -> st { reservedBuiltinNames = 
                                reservedBuiltinNames st ++ 
                                fromMaybe [] (lookup name builtinReservedNames) })
        return (opt, name)
    extendSig (name, Nothing, opt) = do
        _ <- symbol name
        return (opt, name)
    builtinTheory = asum $ map (try . extendSig) builtinsNames

diffbuiltins :: Parser ()
diffbuiltins =
    (symbol "builtins" *> colon *> commaSep1 builtinTheory) Data.Functor.$> ()
  where
    extendSig (name, msig) =
        symbol name *>
        modifyStateSig (`mappend` msig)
    builtinTheory = asum $ map (try . extendSig) builtinsDiffNames


functionType :: Parser ([SapicType], SapicType)
functionType = try (do
                    _  <- opSlash
                    k  <- fromIntegral <$> natural
                    return (replicate k defaultSapicType, defaultSapicType)
                   )
                <|>(do
                    argTypes  <- parens (commaSep typep)
                    _         <- colon
                    outType   <- typep
                    return (argTypes, outType)
                    )

-- | Parse a 'FunctionAttribute'.
functionAttribute :: Parser FunctionAttribute
functionAttribute = asum
  [ symbol "private" Data.Functor.$> FunctionPrivate
  , symbol "constructor" Data.Functor.$> FunctionConstructor
  , symbol "destructor" Data.Functor.$> FunctionDestructor
  , symbol "data" Data.Functor.$> FunctionData
  ]

getReservedNames :: MaudeSig -> [String]
getReservedNames msig = 
  map (BC.unpack . fst) (S.toList $ stFunSyms msig)

-- Map builtin names to their reserved function names
builtinReservedNames :: [(String, [String])]
builtinReservedNames = 
  [(name, getReservedNames msig) | (name, Just msig, _) <- builtinsNames]

functionDecls :: Parser [SapicFunSym]
functionDecls = do
        f <- BC.pack <$> identifier
        (argTypes,outType) <- functionType
        atts <- option [] $ list functionAttribute
        st <- getState
        sign <- sig <$> getState
        let k = length argTypes
        let priv = if FunctionPrivate `elem` atts then Private else Public
        let destr = if FunctionDestructor `elem` atts then Destructor else Constructor
        let isData = FunctionData `elem` atts
        validateFunctionAttributes f atts
        ensureNameAllowed st sign f (k, priv, destr)
        baseSym <- addOrLookupDeclaredFunction sign f (k, priv, destr)
        if isData
          then do
            let accessorInfos = mkDataAccessorInfos baseSym argTypes outType
            mapM_ (ensureGeneratedAccessorNameAvailable sign . accessorName) accessorInfos
            modifyStateSig $ \sig0 ->
              let sig1 = foldl (flip addFunSym) sig0 (map fst3 accessorInfos)
              in foldl (flip addCtxtStRule) sig1 (mkDataAccessorRules baseSym (map fst3 accessorInfos))
            return ((baseSym, argTypes, outType) : accessorInfos)
          else
            return [(baseSym, argTypes, outType)]
  where
    fst3 (x, _, _) = x
    accessorName ((name, _), _, _) = name

    validateFunctionAttributes name attrs = do
      when (countAttr FunctionData attrs > 1) $
        fail $ "duplicate `data` attribute for `" ++ BC.unpack name ++ "`"
      when (FunctionData `elem` attrs && FunctionDestructor `elem` attrs) $
        fail $ "`" ++ BC.unpack name ++ "` cannot be both `[data]` and `[destructor]`"
      when (FunctionData `elem` attrs && FunctionPrivate `elem` attrs) $
        fail $ "`" ++ BC.unpack name ++ "` cannot be both `[data]` and `[private]`"

    countAttr attr = length . filter (== attr)

    ensureNameAllowed st' sign' name requested = do
      let allReservedNames = reservedBuiltinNames st'
      when (BC.unpack name `elem` allReservedNames) $ do
        let conflictingBuiltins =
              [ builtin
              | (builtin, names) <- builtinReservedNames
              , BC.unpack name `elem` names
              ]
        case lookup name (S.toList $ stFunSyms sign') of
          Just builtinSig | builtinSig /= requested ->
            fail $ "`" ++ BC.unpack name ++ "` conflicts with builtin(s) "
                ++ show conflictingBuiltins
                ++ " (builtin: " ++ show builtinSig
                ++ ", requested: " ++ show requested ++ ")"
          _ -> pure ()
      case lookup name (S.toList (macroNames sign')) of
        Just _ ->
          fail $ "conflicting definition for `" ++ BC.unpack name ++ "`: this name is already used by a macro"
        Nothing ->
          pure ()

    addOrLookupDeclaredFunction sign' name desired = do
      let (arity, privacy, _) = desired
      case lookup name (S.toList (stFunSyms sign')) of
        Just kp'
          | kp' /= desired
          && (BC.unpack name /= "fst" || arity /= 1 || privacy == Private)
          && (BC.unpack name /= "snd" || arity /= 1 || privacy == Private) ->
          fail $ "conflicting arities/options "
              ++ show kp' ++ " and " ++ show desired
              ++ " for `" ++ BC.unpack name
              ++ "`. Please choose a different name for this function."
        _ -> do
          let sym = (name, desired)
          modifyStateSig $ addFunSym sym
          return sym

    ensureGeneratedAccessorNameAvailable sign' name = do
      st' <- getState
      let allReservedNames = reservedBuiltinNames st'
      when (BC.unpack name `elem` allReservedNames) $ do
        let conflictingBuiltins =
              [ builtin
              | (builtin, names) <- builtinReservedNames
              , BC.unpack name `elem` names
              ]
        fail $ "generated accessor `" ++ BC.unpack name
            ++ "` conflicts with builtin(s) " ++ show conflictingBuiltins
      when (BC.unpack name `elem` reservedBuiltins) $
        fail $ "generated accessor `" ++ BC.unpack name
            ++ "` is a reserved function name for builtins"
      case lookup name (S.toList (stFunSyms sign') ++ S.toList (macroNames sign')) of
        Just _ ->
          fail $ "generated accessor `" ++ BC.unpack name ++ "` conflicts with an existing function or macro"
        Nothing ->
          pure ()

    mkDataAccessorInfos funSym@(_, (arity, _, _)) argTypes outType =
      [ ( accessorSym i
        , [outType]
        , argTypes !! (i - 1)
        )
      | i <- [1 .. arity]
      ]
      where
        accessorSym i = (mkAccessorName (fst funSym) i, (1, Public, Destructor))

    mkDataAccessorRules funSym@(_, (arity, _, _)) accessorSyms =
      [ accessorRule i accessorSym
      | (i, accessorSym) <- zip [1 .. arity] accessorSyms
      ]
      where
        vars =
          [ varTerm $ LVar "x" LSortMsg (fromIntegral i)
          | i <- [1 .. arity]
          ]
        funTerm = fAppNoEq funSym vars
        accessorRule i accessorSym =
          fAppNoEq accessorSym [funTerm] `CtxtStRule`
            StRhs [[0, i - 1]] (vars !! (i - 1))

    mkAccessorName base idx = base <> BC.pack ('_' : show idx)


functions :: Parser [SapicFunSym]
functions =
    (try (symbol "functions") <|> symbol "function") *> colon *> fmap concat (commaSep1 functionDecls)

equations :: Parser ()
equations = do
    convergent <- option False (try $ do
        _ <- symbol "equations"
        _ <- brackets (symbol "convergent")
        colon
        return True)
    unless convergent $ symbol "equations" *> colon
    eqs <- commaSep1 equation
    modifyStateSig (\sig -> foldl (flip addCtxtStRule) sig eqs)
    modifyState (\st -> st { sig = (sig st) { eqConvergent = convergent } })  -- Explicit state update
    return ()
  where
    equation = do
        rrule <- RRule <$> term llitNoPub True <*> (equalSign *> term llitNoPub True)
        case rRuleToCtxtStRule rrule of
          Just str -> return str
          Nothing  -> fail $ "Not a correct equation: " ++ show rrule

-- | options
options :: OpenTheory -> Parser OpenTheory
options thy0 =do
            _  <- symbol "options"
            _  <- colon
            l <- commaSep1 builtinTheory -- l is list of lenses to set options to true with
                                         -- builtinTheory modifies signature in state.
            return $ foldl setOption' thy0 l
  where
    setOption' thy Nothing  = thy
    setOption' thy (Just l) = setOption l thy
    builtinTheory = asum
      [  try 
         (symbol "translation-progress") Data.Functor.$> Just transProgress
        , symbol "translation-allow-pattern-lookups" Data.Functor.$> Just transAllowPatternMatchinginLookup
        , symbol "translation-state-optimisation" Data.Functor.$> Just stateChannelOpt
        , symbol "translation-asynchronous-channels" Data.Functor.$> Just asynchronousChannels
        , symbol "translation-compress-events" Data.Functor.$> Just compressEvents
      ]

predicate :: Parser Predicate
predicate = do
           f <- fact' lvar
           _ <- symbol "<=>"
           Predicate f <$> plainFormula
           <?> "predicate declaration"

preddeclaration :: OpenTheory -> Parser OpenTheory
preddeclaration thy = do
                    _          <- try (symbol "predicates" <|> symbol "predicate")
                    _          <- colon
                    predicates <- commaSep1 predicate
                    foldM liftedAddPredicate thy predicates
                    <?> "predicate block"

-- | parse an export declaration
export :: OpenTheory -> Parser OpenTheory
export thy = do
                    _          <- try (symbol "export")
                    tag          <- identifier
                    _          <- colon
                    text       <- doubleQuoted $ many bodyChar -- TODO Gotta use some kind of text.
                    let ei = ExportInfo tag text
                    return (addExportInfo ei thy)
                    <?> "export block"
              where
                bodyChar = try $ do
                  c <- anyChar
                  case c of
                    '\\' -> char '\\' <|> char '"'
                    '"'  -> mzero
                    _    -> return c


heuristic :: Bool -> Maybe FilePath -> Parser [GoalRanking ProofContext]
heuristic diff workDir = symbol "heuristic" *> char ':' *> skipMany (char ' ') *> (concat <$> many1 (goalRanking diff workDir)) <* lexeme spaces

goalRanking :: Bool -> Maybe FilePath -> Parser [GoalRanking ProofContext]
goalRanking diff workDir = try oracleRanking <|> internalTacticRanking <|> regularRanking <?> "proof method ranking"
   where
       regularRanking = filterHeuristic diff <$> many1 letter <* skipMany (char ' ')

       internalTacticRanking = do
            _ <- string "{" <* skipMany (char ' ')
            goal <- toGoalRanking <$> pure ("{.}")
            tacticName <- optionMaybe (many1 (noneOf "\"\n\r{}") <* char '}' <* skipMany (char ' '))

            return $ [mapInternalTacticRanking (maybeSetInternalTacticName tacticName) goal]

       oracleRanking = do
           goal <- toGoalRanking <$> (string "o" <|> string "O") <* skipMany (char ' ')
           relPath <- optionMaybe (char '"' *> many1 (noneOf "\"\n\r") <* char '"' <* skipMany (char ' '))

           return [mapOracleRanking (maybeSetOracleRelPath relPath . maybeSetOracleWorkDir workDir) goal]

       toGoalRanking = if diff then stringToGoalRankingDiff False else stringToGoalRanking False

liftedAddPredicate :: Catch.MonadThrow m =>
                      Theory sig c r p TranslationElement
                      -> Predicate -> m (Theory sig c r p TranslationElement)
liftedAddPredicate thy prd = liftMaybeToEx (DuplicateItem (PredicateItem prd)) (addPredicate prd thy)
