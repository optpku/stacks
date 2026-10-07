module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_13_2_InverseImage
public import stacks_project.Chap67.Lemma_67_15_3_SchemeTheoreticSupport
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Flat inverse images of scheme-theoretic supports

The inverse image of a scheme-theoretic support of a finite-type quasi-coherent
module along a flat morphism of algebraic spaces is again a scheme-theoretic
support.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

namespace IsSchemeTheoreticSupport

/-- Lemma 67.30.10: Let `S` be a scheme. Let `f : Y ⟶ X` be a morphism of
algebraic spaces over `S`. Let `F` be a finite type quasi-coherent `𝒪_X`-module
with scheme-theoretic support `i : Z ⟶ X`. If `f` is flat, then
`inverseImageι f i` is a scheme-theoretic support of `(pullback f).obj F`. -/
@[stacks 089C]
instance pullback_of_flat {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) [Flat f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsSchemeTheoreticSupport F i] :
    IsSchemeTheoreticSupport ((pullback f).obj F) (inverseImageι f i) :=
  sorry

/-- Scheme-theoretic support of a finite-type quasi-coherent module is preserved
by pullback along a flat morphism of algebraic spaces, as a statement about
chosen pullbacks. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
    {f : Y ⟶ X} {i : Z ⟶ X} {pY : P ⟶ Y} {pZ : P ⟶ Z}
    (h : IsPullback pY pZ f i) [Flat f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] [IsClosedImmersion i]
    [IsSchemeTheoreticSupport F i] :
    IsSchemeTheoreticSupport ((pullback f).obj F) pY :=
  sorry

end IsSchemeTheoreticSupport

end AlgebraicGeometry.AlgebraicSpace.Modules
