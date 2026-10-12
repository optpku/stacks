/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Projections
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap74.Lemma_74_7_1_InverseImage
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap100.Lemma_100_9_14_Union

/-!
# Source locus of a representable morphism of algebraic stacks

The largest open substack of the source on which a 1-morphism has a morphism
property `P` is the union of all open substacks with that property. Base change
of an open substack along a 2-fibre product is the induced open immersion of
apices.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An open subspace `W ⊂ X` is a largest source open for `P` along `f` when
`f` restricted to `W` has `P`, and every open subspace with that property is
contained in `W` on points. -/
structure IsLargestSourceOpen {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (W : OpenSubspace X) : Prop where
  /-- The restriction of `f` to `W` has `P`. -/
  hasP : P (W.ι ≫ f)
  /-- Every open subspace on which `f` has `P` is contained in `W` on points. -/
  maximal :
    ∀ U : OpenSubspace X, P (U.ι ≫ f) → U.pointsSet ⊆ W.pointsSet

/-- `W` is a largest source open for `P` along `f` if and only if the restriction
has `P` and every competing open is contained in `W` on points. -/
theorem IsLargestSourceOpen_iff {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (W : OpenSubspace X) :
    IsLargestSourceOpen P f W ↔
      P (W.ι ≫ f) ∧
        ∀ U : OpenSubspace X, P (U.ι ≫ f) → U.pointsSet ⊆ W.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.Groupoids.Hom

/-- An open substack `U ⊂ X` is a largest source open for `P` along `f` when
`f` restricted to `U` has `P`, and every open substack with that property is
contained in `U` as an `objectProperty`. -/
structure IsLargestSourceOpenStack {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    [AlgebraicStack X] (f : X ⟶ Y) (U : AlgebraicStack.OpenSubstack X) : Prop where
  /-- The restriction of `f` to `U` has `P`. -/
  hasP : has P (U.ι ≫ f)
  /-- Every open substack on which `f` has `P` is contained in `U`. -/
  maximal :
    ∀ V : AlgebraicStack.OpenSubstack X,
      has P (V.ι ≫ f) → V.objectProperty ≤ U.objectProperty

/-- `U` is a largest source open substack for `P` along `f` if and only if the
restriction has `P` and every competing open substack is contained in `U`. -/
theorem IsLargestSourceOpenStack_iff {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    [AlgebraicStack X] (f : X ⟶ Y) (U : AlgebraicStack.OpenSubstack X) :
    IsLargestSourceOpenStack P f U ↔
      has P (U.ι ≫ f) ∧
        ∀ V : AlgebraicStack.OpenSubstack X,
          has P (V.ι ≫ f) → V.objectProperty ≤ U.objectProperty :=
  sorry

/-- The family of open substacks of `X` on which `f` has `P`. -/
def sourceLocusFamily {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y) :
    {U : AlgebraicStack.OpenSubstack X // has P (U.ι ≫ f)} →
      AlgebraicStack.OpenSubstack X :=
  Subtype.val

/-- The source locus of `f` for `P`: the union of all open substacks of `X` on
which `f` has `P`. -/
def sourceLocus {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y) :
    AlgebraicStack.OpenSubstack X :=
  AlgebraicStack.OpenSubstack.iUnion (sourceLocusFamily P f)

/-- The source locus is the `iUnion` of the open substacks on which `f` has `P`. -/
theorem sourceLocus_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y) :
    (sourceLocus P f).objectProperty =
      AlgebraicStack.OpenSubstack.objectProperty_iUnion (sourceLocusFamily P f) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom

namespace AlgebraicGeometry.AlgebraicStack.OpenSubstack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The cospan transformation `(U.ι ≫ f, g) ⟶ (f, g)` with left leg `U.ι`,
right leg `𝟙 Z`, and base `𝟙 Y`. -/
def pullbackCospan (U : OpenSubstack X) {Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    CospanTransform (U.ι ≫ f) g f g :=
  CospanTransform.mk U.ι (𝟙 Z) (𝟙 Y) (ρ_ (U.ι ≫ f)).symm
    (λ_ g ≪≫ (ρ_ g).symm)

/-- The 1-morphism `Z ×_Y U ⟶ Z ×_Y X` induced by `U.ι` and `𝟙 Z`. -/
def pullbackι (U : OpenSubstack X) {Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} (U.ι ≫ f) g ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g :=
  TwoFibreProduct.map.{u + 1, u, u + 1, u} (pullbackCospan U f g)

/-- The inverse image of an open substack `U ⊂ X` along the 2-fibre product of
`f : X ⟶ Y` with `g : Z ⟶ Y`, as an open substack of `Z ×_Y X`. -/
def pullback (U : OpenSubstack X) {Y Z : GroupoidsOver S}
    [AlgebraicStack Y] [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) :
    OpenSubstack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) where
  Y := TwoFibreProduct.apex.{u + 1, u, u + 1, u} (U.ι ≫ f) g
  ι := pullbackι U f g
  isAlgebraicStack := inferInstance
  isOpenImmersion := sorry
  isStrictlyFull := sorry

/-- The inverse-image inclusion is a strictly full open immersion whose source
is the 2-fibre product of `U.ι ≫ f` with `g`. -/
theorem pullback_spec (U : OpenSubstack X) {Y Z : GroupoidsOver S}
    [AlgebraicStack Y] [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) :
    OpenImmersion (U.pullback f g).ι ∧ IsStrictlyFull (U.pullback f g).ι :=
  sorry

end AlgebraicGeometry.AlgebraicStack.OpenSubstack
