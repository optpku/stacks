/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap73.Definition_73_4_1_Precoverage

/-!
# Étale morphisms are étale local on the source

Étaleness of morphisms of algebraic spaces is local on the source for the
étale precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

/-- Étaleness of morphisms of algebraic spaces is local on the source for
the étale precoverage. -/
instance isLocalAtSourceEtale {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@Etale S : MorphismProperty (AlgebraicSpace S))
      (@etalePrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is étale if and only if it remains so
after precomposition with every member of an étale covering of the source. -/
theorem iff_forall_comp_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (𝒰 : (@etalePrecoverage S).ZeroHypercover X) :
    Etale f ↔ ∀ i, Etale (𝒰.f i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale
