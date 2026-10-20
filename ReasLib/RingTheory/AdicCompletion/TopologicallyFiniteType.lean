/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Over

/-!
# Topologically finite type algebras

An `R`-algebra `S` is topologically of finite type with respect to an ideal `I`
when it is `I`-adically complete and its special fiber is of finite type over `R ⧸ I`.
-/

@[expose] public section

universe v u

namespace Algebra

variable {R : Type u} [CommRing R] (I : Ideal R) (S : Type v) [CommRing S] [Algebra R S]

/-- An `R`-algebra `S` is topologically of finite type with respect to an ideal `I`
if it is `I`-adically complete and the special fiber `S ⧸ I S` is of finite type
over `R ⧸ I`. -/
class TopologicallyFiniteType : Prop where
  /-- The algebra is `I`-adically complete as an `R`-module. -/
  isAdicComplete : IsAdicComplete I S
  /-- The special fiber `S ⧸ I S` is of finite type over `R ⧸ I`. -/
  finiteType_quotient : FiniteType (R ⧸ I) (S ⧸ I.map (algebraMap R S))

namespace TopologicallyFiniteType

attribute [instance] isAdicComplete finiteType_quotient

/-- Combine `I`-adic completeness and finite type of the special fiber. -/
instance instOfIsAdicCompleteFiniteType
    [IsAdicComplete I S] [FiniteType (R ⧸ I) (S ⧸ I.map (algebraMap R S))] :
    TopologicallyFiniteType I S where
  isAdicComplete := ‹_›
  finiteType_quotient := ‹_›

/-- An `R`-algebra is topologically of finite type with respect to `I` if and only if it is
`I`-adically complete and its special fiber is of finite type over `R ⧸ I`. -/
theorem iff :
    TopologicallyFiniteType I S ↔
      IsAdicComplete I S ∧ FiniteType (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  ⟨fun h ↦ ⟨h.isAdicComplete, h.finiteType_quotient⟩, fun h ↦ ⟨h.1, h.2⟩⟩

end TopologicallyFiniteType

end Algebra
