/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap74.Lemma_74_16_1_LocalAtSource

/-!
# Local finite type is fppf local on the source

Locally of finite type for morphisms of algebraic spaces is local on the
source for the fppf precoverage.

The canonical algebraic-space `fppfPrecoverage` owner currently rebuilds the
broken `Chap66.Lemma_66_4_2_Comparison`. This module reuses the reconstructed
étale-scheme-square flatness class and fppf precoverage from Lemma 74.16.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType

/-- Local finite type of morphisms of algebraic spaces is local on the source
for the fppf precoverage. -/
instance isLocalAtSourceFppf {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is locally of finite type if and only if it
remains so after precomposition with every member of an fppf covering of the
source. -/
theorem iff_forall_comp_fppf {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (𝒰 : (fppfPrecoverage S).ZeroHypercover X) :
    LocallyOfFiniteType f ↔ ∀ i, LocallyOfFiniteType (𝒰.f i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType
