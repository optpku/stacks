/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap61.Lemma_61_12_19_Pullback
public import stacks_project.Chap61.Lemma_61_12_21_AffineIndEtale

/-!
# Base change of affine ind-étale objects along a closed immersion

Fibre product with a closed immersion of affine schemes preserves affine
ind-étale objects of the small pro-étale site, yielding a continuous functor
`u : AffineIndEtale X ⥤ AffineIndEtale Z`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]

/-- Pullback along a closed immersion of affines preserves affine ind-étale
objects of the small pro-étale site. -/
theorem AffineIndEtale.objects_map_baseChange (i : Z ⟶ X) [IsClosedImmersion i]
    (U : AffineIndEtale X) :
    affineIndEtaleObjects Z
      ((affineIndEtaleInclusion X ⋙ smallProetalePullback i).obj U) := sorry

/-- Base change of affine ind-étale objects along a closed immersion, sending
`U` to `U ×_X Z`. -/
def AffineIndEtale.baseChange (i : Z ⟶ X) [IsClosedImmersion i] :
    AffineIndEtale X ⥤ AffineIndEtale Z :=
  (affineIndEtaleObjects Z).lift (affineIndEtaleInclusion X ⋙ smallProetalePullback i)
    (objects_map_baseChange i)

/-- Affine ind-étale base change sits over pro-étale base change via the
inclusions. -/
def AffineIndEtale.baseChange_comp_inclusion (i : Z ⟶ X) [IsClosedImmersion i] :
    AffineIndEtale.baseChange i ⋙ affineIndEtaleInclusion Z ≅
      affineIndEtaleInclusion X ⋙ smallProetalePullback i :=
  (affineIndEtaleObjects Z).liftCompιIso
    (affineIndEtaleInclusion X ⋙ smallProetalePullback i)
    (objects_map_baseChange i)

/-- The inclusion comparison is the canonical full-subcategory lift isomorphism. -/
theorem AffineIndEtale.baseChange_comp_inclusion_eq (i : Z ⟶ X)
    [IsClosedImmersion i] :
    baseChange_comp_inclusion i =
      (affineIndEtaleObjects Z).liftCompιIso
        (affineIndEtaleInclusion X ⋙ smallProetalePullback i)
        (objects_map_baseChange i) := sorry

/-- The underlying scheme of affine ind-étale base change is the fibre product
over `X`. -/
theorem AffineIndEtale.baseChange_obj (i : Z ⟶ X) [IsClosedImmersion i]
    (U : AffineIndEtale X) :
    ((AffineIndEtale.baseChange i).obj U).obj.left =
      Limits.pullback U.obj.hom i := sorry

/-- Affine ind-étale base change is continuous for the affine ind-étale
topologies. -/
instance AffineIndEtale.baseChange_isContinuous (i : Z ⟶ X)
    [IsClosedImmersion i] :
    Functor.IsContinuous (AffineIndEtale.baseChange i)
      (affineIndEtaleTopology X) (affineIndEtaleTopology Z) := sorry

end AlgebraicGeometry.Scheme.ProEt
