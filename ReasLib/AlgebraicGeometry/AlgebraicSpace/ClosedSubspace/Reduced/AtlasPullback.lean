/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.AtlasImage
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-! # The reduced atlas as an image-sheaf pullback

The reduced atlas represents the pullback of its image sheaf to the ambient étale atlas.
The comparison and its inverse are given by the image factorization and closed-immersion lift.
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

/-- The reduced atlas map to the ambient space factors through its image sheaf. -/
theorem chart_commutes :
    (toImage X Z).hom ≫ (inclusion X Z).hom =
      yoneda.map (atlasInclusion X Z) ≫ atlasMap X :=
  congrArg (fun h ↦ h.hom) (factorization X Z)

/-- The comparison to the image-sheaf pullback pairs the image map with the atlas inclusion. -/
def comparison : yoneda.obj (reducedAtlas X Z) ⟶ pullbackPresheaf X Z :=
  pullback.lift (toImage X Z).hom (yoneda.map (atlasInclusion X Z)) (chart_commutes X Z)

/-- The first comparison projection is the reduced atlas map to its image sheaf. -/
@[reassoc]
theorem comparison_fst :
    comparison X Z ≫ pullback.fst (inclusion X Z).hom (atlasMap X) = (toImage X Z).hom :=
  pullback.lift_fst _ _ _

/-- The second comparison projection is the reduced closed inclusion into the atlas. -/
@[reassoc]
theorem comparison_snd :
    comparison X Z ≫ pullback.snd (inclusion X Z).hom (atlasMap X) =
      yoneda.map (atlasInclusion X Z) :=
  pullback.lift_snd _ _ _

/-- The second pullback projection annihilates the ideal of the closed subscheme. -/
private theorem inverse_ker (U : (Over S)ᵒᵖ)
    (p : (pullbackPresheaf X Z).obj U) :
    (atlasInclusion X Z).left.ker ≤
      ((pullback.snd (inclusion X Z).hom (atlasMap X)).app U p).left.ker := by
  sorry

/-- Lift the second pullback projection through the closed subscheme. -/
private def inverseApp (U : (Over S)ᵒᵖ)
    (p : (pullbackPresheaf X Z).obj U) : U.unop ⟶ reducedAtlas X Z := by
  let j := (ideal X Z).subschemeι
  let q := (pullback.snd (inclusion X Z).hom (atlasMap X)).app U p
  let hClosed : AlgebraicGeometry.IsClosedImmersion j :=
    AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion _
      ((ideal X Z).range_subschemeι ▸ (ideal X Z).support.isClosed)
  exact Over.homMk
    (@AlgebraicGeometry.IsClosedImmersion.lift _ _ _ j q.left hClosed
      (inverse_ker X Z U p)) (by
        change (@AlgebraicGeometry.IsClosedImmersion.lift _ _ _ j q.left hClosed
          (inverse_ker X Z U p)) ≫ (j ≫ (atlasScheme X).hom) = U.unop.hom
        rw [← Category.assoc,
          @AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _ j q.left hClosed
            (inverse_ker X Z U p)]
        exact Over.w q)

/-- The closed-subscheme lifts commute with restriction along test morphisms. -/
private theorem inverse_naturality {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (pullbackPresheaf X Z).map f ≫ TypeCat.ofHom (inverseApp X Z V) =
      TypeCat.ofHom (inverseApp X Z U) ≫ (yoneda.obj (reducedAtlas X Z)).map f := by
  sorry

/-- The inverse comparison lifts the second projection through the closed subscheme. -/
@[no_expose] def comparisonInverse : pullbackPresheaf X Z ⟶ yoneda.obj (reducedAtlas X Z) where
  app U := TypeCat.ofHom (inverseApp X Z U)
  naturality _ _ f := private inverse_naturality X Z f

/-- The comparison followed by its explicit inverse is the identity. -/
theorem comparison_comp_inverse :
    comparison X Z ≫ comparisonInverse X Z = 𝟙 (yoneda.obj (reducedAtlas X Z)) := by
  sorry

/-- The explicit inverse followed by the comparison is the identity. -/
theorem inverse_comp_comparison :
    comparisonInverse X Z ≫ comparison X Z = 𝟙 (pullbackPresheaf X Z) := by
  sorry

/-- The closed subscheme represents the image-sheaf pullback via the two explicit comparisons. -/
def comparisonIso : yoneda.obj (reducedAtlas X Z) ≅ pullbackPresheaf X Z where
  hom := comparison X Z
  inv := comparisonInverse X Z
  hom_inv_id := comparison_comp_inverse X Z
  inv_hom_id := inverse_comp_comparison X Z

/-- The canonical comparison to the image-sheaf pullback is an isomorphism. -/
instance comparison_isIso : IsIso (comparison X Z) :=
  (comparisonIso X Z).isIso_hom

/-- The two actual projections specify the representation over the original atlas. -/
theorem comparisonIso_hom_snd :
    (comparisonIso X Z).hom ≫ pullback.snd (inclusion X Z).hom (atlasMap X) =
      yoneda.map (atlasInclusion X Z) := comparison_snd X Z

/-- The first projection of the representing isomorphism is the map to the image sheaf. -/
theorem comparisonIso_hom_fst :
    (comparisonIso X Z).hom ≫ pullback.fst (inclusion X Z).hom (atlasMap X) =
      (toImage X Z).hom := comparison_fst X Z

/-- The inverse representing comparison followed by the forward comparison is the identity. -/
theorem comparison_inverse_forward :
    (comparisonIso X Z).inv ≫ comparison X Z = 𝟙 (pullbackPresheaf X Z) :=
  (comparisonIso X Z).inv_hom_id

end AlgebraicGeometry.AlgebraicSpace.ReducedClosed.AtlasPullback

