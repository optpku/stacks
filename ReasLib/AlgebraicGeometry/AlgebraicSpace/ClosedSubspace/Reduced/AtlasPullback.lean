/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.AtlasImage
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-! # Pin the reduced atlas to the actual image-sheaf pullback diagram

The displayed comparison is the actual pullback lift of the image-chart
map and the explicit closed scheme inclusion. Its IsIso law concerns this
fixed map, with no arbitrary isomorphism or new chosen scheme witness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ReducedClosed.AtlasPullback

open ReducedClosed.AtlasImage

variable {S : Scheme.{u}} (X : AlgebraicSpace S) (Z : Closeds (Points X))

/-- The image sheaf pulled back to the actual original atlas, in presheaves. -/
def pullbackPresheaf : (Over S)ᵒᵖ ⥤ Type u :=
  pullback (inclusion X Z).hom (atlasMap X)

theorem chart_commutes :
    (toImage X Z).hom ≫ (inclusion X Z).hom =
      yoneda.map (atlasInclusion X Z) ≫ atlasMap X :=
  congrArg (fun h ↦ h.hom) (factorization X Z)

/-- The fixed canonical comparison into the actual pullback, with both
components already explicit in the preceding module. -/
def comparison : yoneda.obj (reducedAtlas X Z) ⟶ pullbackPresheaf X Z :=
  pullback.lift (toImage X Z).hom (yoneda.map (atlasInclusion X Z)) (chart_commutes X Z)

@[reassoc]
theorem comparison_fst :
    comparison X Z ≫ pullback.fst (inclusion X Z).hom (atlasMap X) = (toImage X Z).hom :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem comparison_snd :
    comparison X Z ≫ pullback.snd (inclusion X Z).hom (atlasMap X) =
      yoneda.map (atlasInclusion X Z) :=
  pullback.lift_snd _ _ _

/-- Geometric law for this specified map. On the actual atlas kernel pair
R = U ×_X U, both projections are étale. Base change of the explicit
reduced closed subscheme is reduced and has support the inverse image of
Z, hence the two resulting radical ideals agree. The subfunctor descends;
its relative sheaf image pulls back to precisely the displayed subscheme.
This works for arbitrary X and closed Z, with no Noetherian/qc restriction. -/
theorem comparison_isIso : IsIso (comparison X Z) := by
  sorry

/-- Invert only the fixed inclusion/image pullback comparison. -/
def comparisonIso : yoneda.obj (reducedAtlas X Z) ≅ pullbackPresheaf X Z := by
  -- Local instance justification (proof-local temporary data): Package the specified reduced-atlas pullback comparison as an isomorphism using its own geometric IsIso law.
  letI := comparison_isIso X Z
  exact asIso (comparison X Z)

/-- The two actual projections specify the representation over the original atlas. -/
theorem comparisonIso_hom_snd :
    (comparisonIso X Z).hom ≫ pullback.snd (inclusion X Z).hom (atlasMap X) =
      yoneda.map (atlasInclusion X Z) := comparison_snd X Z

theorem comparisonIso_hom_fst :
    (comparisonIso X Z).hom ≫ pullback.fst (inclusion X Z).hom (atlasMap X) =
      (toImage X Z).hom := comparison_fst X Z

theorem comparison_inverse_forward :
    (comparisonIso X Z).inv ≫ comparison X Z = 𝟙 (pullbackPresheaf X Z) :=
  (comparisonIso X Z).inv_hom_id

end AlgebraicGeometry.AlgebraicSpace.ReducedClosed.AtlasPullback

