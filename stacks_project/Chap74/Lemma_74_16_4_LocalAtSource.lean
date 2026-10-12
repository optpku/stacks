/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage

/-!
# Universal openness is fppf local on the source

Universally open morphisms of algebraic spaces are local on the source for the
fppf precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

/-- Universal openness of morphisms of algebraic spaces is local on the source
for the fppf precoverage. -/
instance isLocalAtSourceFppf {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@UniversallyOpen S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is universally open if and only if it remains
so after precomposition with every member of an fppf covering of the source. -/
theorem iff_forall_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (𝒰 : (fppfPrecoverage S).ZeroHypercover X) :
    UniversallyOpen f ↔ ∀ i, UniversallyOpen (𝒰.f i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.UniversallyOpen
