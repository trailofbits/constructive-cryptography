import Informalization.Semantics.Symbols

namespace Tests.Symbols

open Lean
open Informalization.Semantics.Symbols

private def querySetKey : Key := {
  role := .querySet
  source := mkConst ``Nat
}

private def secondSetKey : Key := {
  role := .querySet
  source := mkConst ``Int
}

private def sampleSizeKey : Key := {
  role := .sampleSize
  source := mkConst ``String
}

private def queryBudgetKey : Key := {
  role := .queryBudget
  source := mkConst ``Nat.succ
}

private def symbolFixture : Bool :=
  let root : Scope := {}
  let (root, first) := root.introduce querySetKey "S"
  let child := root.child
  let (child, reused) := child.introduce querySetKey "T"
  let (child, fresh) := child.introduce secondSetKey "S"
  let (grandchild, sample) := child.child.introduce sampleSizeKey "k"
  let (grandchild, budget) := grandchild.introduce queryBudgetKey "q"
  first == "S" && reused == "S" && fresh == "S_{1}" && sample == "k" &&
    budget == "q" &&
    root.lookup? querySetKey == some "S" &&
    root.lookup? secondSetKey == none &&
    child.lookup? secondSetKey == some "S_{1}" &&
    child.lookup? sampleSizeKey == none &&
    grandchild.lookup? sampleSizeKey == some "k"

#guard symbolFixture

/-- Independently retained Lean proof contexts copy theorem binders to fresh
free-variable identifiers.  Their stable user names must nevertheless retain
one paper symbol throughout the reader. -/
private def copiedBinderFixture : Bool :=
  let rootKey : Key := {
    role := .queryBudget
    source := mkFVar ⟨`rootQ⟩
    binderName? := some `q
  }
  let copiedKey : Key := {
    role := .queryBudget
    source := mkFVar ⟨`copiedQ⟩
    binderName? := some `q
  }
  let otherKey : Key := {
    role := .queryBudget
    source := mkFVar ⟨`otherQ⟩
    binderName? := some `r
  }
  let (root, rootSymbol) := (default : Scope).introduce rootKey "q"
  let (child, copiedSymbol) := root.child.introduce copiedKey "q"
  let (child, otherSymbol) := child.introduce otherKey "q"
  rootSymbol == "q" && copiedSymbol == "q" && otherSymbol == "q_{1}" &&
    child.lookup? copiedKey == some "q" &&
    child.bindings.any fun binding => binding.key.source == copiedKey.source

#guard copiedBinderFixture

end Tests.Symbols
