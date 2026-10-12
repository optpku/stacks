/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap73.Definition_73_4_1_Precoverage

/-!
# Locally quasi-finite morphisms are étale local on the source

Stacks locally quasi-finite morphisms of algebraic spaces — locally of finite
type and locally quasi-finite — are local on the source for the étale
precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FiniteType

/-- Locally quasi-finite morphisms of algebraic spaces, in the Stacks sense of
locally of finite type and locally quasi-finite, are local on the source for
the étale precoverage. -/
instance locallyQuasiFiniteIsLocalAtSourceEtale {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S))
      (@etalePrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is locally quasi-finite in the Stacks sense
if and only if it remains so after precomposition with every member of an étale
covering of the source. -/
theorem locallyQuasiFinite_iff_forall_comp_etale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒰 : (@etalePrecoverage S).ZeroHypercover X) :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
      ∀ i, LocallyOfFiniteType (𝒰.f i ≫ f) ∧ LocallyQuasiFinite (𝒰.f i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FiniteType
