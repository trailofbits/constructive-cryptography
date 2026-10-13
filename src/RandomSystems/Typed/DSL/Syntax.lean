import Lean

/-!
# Surface syntax

Indentation-based declarations of interfaces, systems, converters and filters, and their effect
statements. Pure expressions, types and proofs use Lean's own parsers.
-/

namespace SystemAlgebra.DSL

open Lean Parser

declare_syntax_cat cryptoStmt
declare_syntax_cat cryptoMember (behavior := both)
declare_syntax_cat cryptoParam
declare_syntax_cat cryptoPort
declare_syntax_cat cryptoCase

/-- A header or right-hand side cannot consume the following indented block.
Parentheses retain Lean's ordinary multiline expression syntax. -/
def lineTerm : Parser := withPosition (categoryParser `term 0)

def cryptoPattern : Parser := withForbidden "→" (categoryParser `term 0)

syntax cryptoArg := ident " : " term
syntax (name := explicitParam) "(" ident+ " : " term ")" : cryptoParam
syntax (name := instanceParam) "[" term "]" : cryptoParam
syntax cryptoTarget := ident <|> ("(" ident,+ ")")

syntax (name := oracleCall) ident noWs "(" term,* ")" : term

macro_rules
  | `($f:ident($args,*)) => `($f:ident $args*)

def cryptoBlock := leading_parser
  many1Indent (ppLine >> categoryParser `cryptoStmt 0)

def cryptoCases := leading_parser
  many1Indent (ppLine >> categoryParser `cryptoCase 0)

syntax (name := assignStmt) cryptoTarget (" : " term)? " ← " lineTerm : cryptoStmt
syntax (name := sampleStmt) cryptoTarget (" : " term)? " ←$ " lineTerm : cryptoStmt
syntax (name := returnStmt) "return " lineTerm : cryptoStmt
syntax (name := ifStmt) "if " lineTerm cryptoBlock ("else" cryptoBlock)? : cryptoStmt
syntax (name := forStmt) "for " ident " ∈ " lineTerm cryptoBlock : cryptoStmt
syntax (name := matchStmt) "match " lineTerm cryptoCases : cryptoStmt
syntax (name := caseStmt) "| " cryptoPattern " →" cryptoBlock : cryptoCase

syntax (name := portDecl) ident "(" cryptoArg,* ")" " → " lineTerm : cryptoPort
syntax (name := oracleDecl) "on " ident "(" cryptoArg,* ")" " → " lineTerm
  cryptoBlock : cryptoMember
syntax (name := initializeDecl) "initialize" cryptoBlock : cryptoMember
syntax (name := requiresDecl) "requires " ident " : " lineTerm : cryptoMember
syntax (name := domainDecl) "domain " ident " ↦ " lineTerm : cryptoMember
syntax (name := insideDecl) "inside " ident " : " lineTerm : cryptoMember

def cryptoMembers := leading_parser
  many1Indent (ppLine >> categoryParser `cryptoMember 0)

def cryptoPorts := leading_parser
  many1Indent (ppLine >> categoryParser `cryptoPort 0)

syntax (name := interfaceDecl) "interface " ident cryptoParam* cryptoPorts : command
syntax (name := systemComponentDecl) "system " ident cryptoParam* cryptoMembers
  ("by" tacticSeq)? : command
syntax (name := systemComponentTypedDecl) "system " ident cryptoParam* " : " lineTerm cryptoMembers
  ("by" tacticSeq)? : command
syntax (name := converterDecl) "converter " ident cryptoParam* cryptoMembers : command
syntax (name := converterTypedDecl) "converter " ident cryptoParam* " : " lineTerm cryptoMembers :
  command
syntax (name := systemDecl) "system " ident cryptoParam* " ≔ " term : command
syntax (name := filterDecl) "filter " ident cryptoParam* " : " lineTerm
  "domain " ident " ↦ " lineTerm ("by" tacticSeq)? : command

end SystemAlgebra.DSL
