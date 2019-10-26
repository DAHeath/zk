module Parser where

import           Control.Applicative
import           Data.Functor.Identity

import           Text.Parsec hiding ((<|>))
import           Text.Parsec.String
import           Text.Parsec.Expr
import           Text.Parsec.Token
import           Text.Parsec.Language

import qualified Language.Haskell.TH as TH

import           Term

def :: GenLanguageDef String u Identity
def = emptyDef { commentStart = "{-"
               , commentEnd = "-}"
               , identStart = letter
               , identLetter = alphaNum
               , opStart = oneOf "~&=:+*^,"
               , opLetter = oneOf "~&=:+*^,"
               , reservedOpNames = ["~", "&", "+", "*", "^", "=", ","]
               , reservedNames = ["let", "in", "fst", "snd", "unit", "cons", "proj"]
               }

TokenParser{ parens = m_parens
           , identifier = m_identifier
           , reservedOp = m_reservedOp
           , reserved = m_reserved
           , semiSep1 = m_semiSep1
           , whiteSpace = m_whiteSpace } = makeTokenParser def

expr :: Parser Term
expr = buildExpressionParser table pterm <?> "expression"

table :: [[Operator String u Identity Term]]
table = [ [Prefix (m_reservedOp "~" >> return Negate)]
        , [Infix (m_reservedOp "&" >> return And) AssocLeft]
        , [Infix (m_reservedOp "*" >> return Add) AssocLeft]
        , [Infix (m_reservedOp "^" >> return Xor) AssocLeft]
        , [Infix (m_reservedOp "+" >> return Mul) AssocLeft]
        ]

pat :: Parser Pat
pat = (PUnit <$ m_reserved "unit")
  <|> (PVar <$> m_identifier)
  <|> pair PPair pat

pair :: (a -> a -> a) -> Parser a -> Parser a
pair f ac = try (m_parens (do
    x <- ac
    m_reservedOp ","
    y <- ac
    pure (f x y)))

pterm :: Parser Term
pterm = pair Pair pterm
   <|> m_parens expr
   <|> (do m_reserved "let"
           p <- pat
           m_reservedOp "="
           t0 <- pterm
           m_reserved "in"
           t1 <- pterm
           pure (Let p t0 t1))
   <|> (m_reserved "fst" >> Fst <$> pterm)
   <|> (m_reserved "snd" >> Snd <$> pterm)
   <|> (m_reserved "cons" >> Construct <$> pterm)
   <|> (m_reserved "proj" >> Project <$> pterm)
   <|> (Unit <$ m_reserved "unit")
   <|> (Var <$> m_identifier)

parseTerm :: Monad m => (String, Int, Int) -> String -> m Term
parseTerm (file, line, col) s =
    case runParser p () "" s of
      Left err  -> fail $ show err
      Right e   -> return e
  where
    p = do pos <- getPosition
           setPosition .
             flip setSourceName file .
             flip setSourceLine line $
             flip setSourceColumn col pos
           spaces
           e <- expr
           eof
           return e

term :: QuasiQuoter
term =  QuasiQuoter { quoteExp = quoteTermExp, quotePat = quoteTermPat }

quoteExprExp :: String -> TH.ExpQ
quoteExprExp s =  do  loc <- TH.location
                      let pos =  (TH.loc_filename loc,
                                 fst (TH.loc_start loc),
                                 snd (TH.loc_start loc))
                      expr <- parseExpr pos s
                      dataToExpQ (const Nothing `extQ` antiExprExp) expr

antiExprExp :: Expr -> Maybe (TH.Q TH.Exp)
antiExprExp  (AntiExpr v)     = Just $ TH.varE  (TH.mkName v)
antiExprExp  _                = Nothing
