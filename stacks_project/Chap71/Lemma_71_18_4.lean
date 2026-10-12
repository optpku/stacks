/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap71.Definition_71_17_1_Blowup
public import stacks_project.Chap71.Definition_71_18_1_StrictTransform
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Lemma 71.18.4

Pointwise flatness over the center makes the strict transform of an algebraic
space (resp. a quasi-coherent module) coincide with the ambient base change
(resp. the pullback), via invertibility of the canonical closed immersion
(resp. quotient).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.18.4 (1): if `X` is flat over `B` at all points lying over `Z`, then
the canonical closed immersion of the strict transform of `X` into `X ×_B B'`
is an isomorphism. -/
@[stacks 0865]
theorem strictTransform_ι_isIso_of_flatAt_over_center
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (Z : ClosedSubspace B) [IsQuasiCoherent Z.idealSheaf]
    (π : Blowup.along Z) (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement π.hom (Z.inverseImage π.hom) f).ι]
    (hflat : ∀ x : Points X, Points.map f x ∈ Z.pointsSet → FlatAt f x) :
    IsIso (strictTransform π.hom (Z.inverseImage π.hom) f).ι :=
  sorry

/-- Lemma 71.18.4 (2): if a quasi-coherent `𝒪_X`-module `F` is flat over `B` at
all points lying over `Z`, then the canonical quotient from `pr_X^* F` onto
the strict transform of `F` is an isomorphism. -/
@[stacks 0865]
theorem strictTransformπ_isIso_of_flatOverAt_over_center
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (Z : ClosedSubspace B) [IsQuasiCoherent Z.idealSheaf]
    (π : Blowup.along Z) (f : X ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent]
    (hflat : ∀ x : Points X, Points.map f x ∈ Z.pointsSet →
      Modules.flatOverAt F f x) :
    IsIso (strictTransformπ π.hom (Z.inverseImage π.hom) f F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
