/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-isomorphisms of Cochain DG Algebras

This leaf owns the morphism property of quasi-isomorphisms of cochain differential graded
algebras. It is independent of derived categories and restriction or extension of scalars.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.MorphismProperty

universe u v

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- A morphism of cochain differential graded algebras is a quasi-isomorphism when its
underlying cochain map is a quasi-isomorphism. -/
@[stacks 09S6 "quasi-isomorphisms of differential graded algebras"]
def quasiIso : MorphismProperty (CochainDGAlgebra.{u, v} R) :=
  fun _ _ f ↦ _root_.QuasiIso f.toCochainMap

namespace QuasiIso

/-- Membership in the DGA quasi-isomorphism property is the canonical quasi-isomorphism
predicate on the underlying cochain map. -/
theorem iff {A B : CochainDGAlgebra.{u, v} R} (f : A ⟶ B) :
    quasiIso f ↔ _root_.QuasiIso f.toCochainMap := sorry

/-- DGA quasi-isomorphisms contain identity morphisms. -/
instance containsIdentities :
    (quasiIso (R := R) : MorphismProperty (CochainDGAlgebra.{u, v} R)).ContainsIdentities := sorry

/-- DGA quasi-isomorphisms are closed under composition. -/
instance isMultiplicative :
    (quasiIso (R := R) : MorphismProperty (CochainDGAlgebra.{u, v} R)).IsMultiplicative := sorry

/-- DGA quasi-isomorphisms satisfy the two-out-of-three property. -/
instance hasTwoOutOfThree :
    (quasiIso (R := R) : MorphismProperty (CochainDGAlgebra.{u, v} R)).HasTwoOutOfThreeProperty := sorry

/-- DGA quasi-isomorphisms are stable under retracts. -/
instance isStableUnderRetracts :
    (quasiIso (R := R) : MorphismProperty (CochainDGAlgebra.{u, v} R)).IsStableUnderRetracts := sorry

end QuasiIso

section Inference

variable (A : CochainDGAlgebra.{u, v} R)

end Inference

end CochainDGAlgebra
