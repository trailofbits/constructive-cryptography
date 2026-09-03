/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.MassotMiller.English

/-!
# Topology language adapter

Optional ontology and proposition vocabulary used by the Rudin-style examples.
Keeping these registrations outside the default registry prevents unrelated
Lean projects from acquiring topology-specific meanings merely by importing
the generic informalization backend.
-/

namespace Informalization.MassotMiller.Topology

open Lean Meta
open Informalization.MassotMiller
open Informalization.MassotMiller.Ontology

private def lastArgument? (arguments : Array Expr) : Option Expr :=
  arguments.back?

private def adjectiveProposition (kind : Name) (adjective : String) :
    English.PropositionHandler := {
  kind
  run := fun _ expression arguments => do
    let some subject := lastArgument? arguments
      | return some (← Ontology.inlineMath expression)
    return some ((← Ontology.inlineMath subject) ++ " is " ++ adjective)
}

/-- Rudin/topology ontology layered on the domain-neutral mathematical
vocabulary. -/
def ontologyRegistry : Ontology.Registry := {
  propositionHandlers := #[
    Ontology.subjectNoun "TopologicalSpace".toName
      "topological space" "topological spaces",
    Ontology.subjectAdjective "IsOpen".toName "open",
    Ontology.subjectAdjective "IsClosed".toName "closed",
    Ontology.subjectAdjective "Dense".toName "dense"
  ] ++ Ontology.defaultRegistry.propositionHandlers
  typeHandlers := Ontology.defaultRegistry.typeHandlers
}

/-- Complete language configuration for the Rudin/topology domain. -/
def languageConfig : English.Config := {
  ontologyRegistry
  propositionHandlers := #[
    adjectiveProposition "IsOpen".toName "open",
    adjectiveProposition "IsClosed".toName "closed",
    adjectiveProposition "Dense".toName "dense"
  ]
}

end Informalization.MassotMiller.Topology
