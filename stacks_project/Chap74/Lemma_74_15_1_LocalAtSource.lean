/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage

/-!
# Fpqc source-locality of flat morphisms of algebraic spaces

Flatness of morphisms of algebraic spaces is local on the source for the fpqc
precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flat

/-- Flatness of morphisms of algebraic spaces is local on the source for the
fpqc precoverage. -/
instance isLocalAtSourceFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@Flat S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is flat if and only if it is flat after
precomposition with every member of an fpqc covering of the source. -/
theorem fpqc_iff_forall_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (𝒰 : (fpqcPrecoverage S).ZeroHypercover X) :
    Flat f ↔ ∀ i, Flat (𝒰.f i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Flat
