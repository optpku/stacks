module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage

/-!
# Local finite presentation is fppf local on the source

Locally of finite presentation for morphisms of algebraic spaces is local on the
source for the fppf precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation

/-- Local finite presentation of morphisms of algebraic spaces is local on the
source for the fppf precoverage. -/
instance isLocalAtSourceFppf {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is locally of finite presentation if and only
if it remains so after precomposition with every member of an fppf covering of
the source. -/
theorem iff_forall_comp_fppf {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (𝒰 : (fppfPrecoverage S).ZeroHypercover X) :
    LocallyOfFinitePresentation f ↔
      ∀ i, LocallyOfFinitePresentation (𝒰.f i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation
