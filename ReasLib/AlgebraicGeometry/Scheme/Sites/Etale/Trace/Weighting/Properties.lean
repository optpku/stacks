/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.Weighting
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- Weighting traces commute with morphisms of abelian étale sheaves. -/
theorem weightingTrace_natural {w : X → ℤ} (hw : f.IsWeighting w)
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    (lowerShriek f).map ((etaleAbelianSheafPullback f).map φ) ≫
        weightingTrace f hw G =
      weightingTrace f hw F ≫ φ := sorry

/-- The weighting trace as a natural transformation
`f_! ∘ f⁻¹ ⟶ 𝟭` on abelian étale sheaves. -/
def weightingTraceNatTrans {w : X → ℤ} (hw : f.IsWeighting w) :
    etaleAbelianSheafPullback f ⋙ lowerShriek f ⟶
      𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) where
  app F := weightingTrace f hw F
  naturality := fun _ _ φ ↦ weightingTrace_natural f hw φ

/-- Components of `weightingTraceNatTrans` are the sheaf traces
`weightingTrace`. -/
theorem weightingTraceNatTrans_app {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (weightingTraceNatTrans f hw).app F = weightingTrace f hw F := sorry

variable {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]

/-- Left vertical identification of the weighting-trace base-change square:
`g⁻¹ f_! f⁻¹ F ≅ f'_! (g')⁻¹ f⁻¹ F ≅ f'_! (f')⁻¹ g⁻¹ F`, using
`lowerShriekBaseChangeIso` and `etaleAbelianSheafPullback_square`. -/
def weightingTraceBaseChangeIso
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback g).obj
        ((lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F)) ≅
      (lowerShriek f').obj
        ((etaleAbelianSheafPullback f').obj
          ((etaleAbelianSheafPullback g).obj F)) :=
  (lowerShriekBaseChangeIso_app f g f' g' h_cart
      ((etaleAbelianSheafPullback f).obj F)).trans
    ((lowerShriek f').mapIso
      ((etaleAbelianSheafPullback_square f g f' g' h_cart).symm.app F))

/-- The weighting trace on the cartesian base change, for the pulled-back
weighting `w ∘ g'`. -/
def weightingTrace_isPullback {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek f').obj ((etaleAbelianSheafPullback f').obj F) ⟶ F :=
  weightingTrace f' (w := fun x' ↦ w (g' x')) (IsWeighting.of_isPullback hw h_cart) F

/-- The forward map of `weightingTraceBaseChangeIso` is the composite of the
lower-shriek base-change isomorphism with the inverse-image square. -/
theorem weightingTraceBaseChangeIso_hom
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (weightingTraceBaseChangeIso f g f' g' h_cart F).hom =
      (lowerShriekBaseChangeIso_app f g f' g' h_cart
          ((etaleAbelianSheafPullback f).obj F)).hom ≫
        (lowerShriek f').map
          ((etaleAbelianSheafPullback_square f g f' g' h_cart).inv.app F) := sorry

/-- Weighting traces commute with arbitrary cartesian base change. -/
theorem weightingTrace_baseChange {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback g).map (weightingTrace f hw F) =
      (weightingTraceBaseChangeIso f g f' g' h_cart F).hom ≫
        weightingTrace_isPullback f g f' g' h_cart hw
          ((etaleAbelianSheafPullback g).obj F) := sorry

end AlgebraicGeometry.Scheme.Etale

end
