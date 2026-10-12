/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Diagram
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

namespace IsConstructibleEtaleSet

/-- A filtered colimit of constructible set-valued étale sheaves with constructible colimit is
essentially constant, with the colimit sheaf as its value in the ind-category. -/
theorem indObject_isEssentiallyConstant
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf X.smallEtaleTopology (Type (u + 1))) [HasColimit F]
    (h_obj : ∀ i,
      IsConstructibleEtaleSet
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (G : Sheaf Y.smallEtaleTopology (Type (u + 1))) ↦
          IsFiniteLocallyConstant G) (F.obj i))
    (h_colim :
      IsConstructibleEtaleSet
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (G : Sheaf Y.smallEtaleTopology (Type (u + 1))) ↦
          IsFiniteLocallyConstant G) (colimit F)) :
      IsFiltered.IsEssentiallyConstant F ∧
      Nonempty (Ind.yoneda.obj (colimit F) ≅ (Ind.lim I).obj F) := sorry

end IsConstructibleEtaleSet

namespace IsConstructibleEtaleAddCommGrp

/-- A filtered colimit of constructible abelian-group-valued étale sheaves with constructible
colimit is essentially constant, with the colimit sheaf as its value in the ind-category. -/

theorem indObject_isEssentiallyConstant
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [HasColimit F]
    (h_obj : ∀ i,
      IsConstructibleEtaleAddCommGrp
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ↦
          IsFiniteLocallyConstantAddCommGrp G) (F.obj i))
    (h_colim :
      IsConstructibleEtaleAddCommGrp
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ↦
          IsFiniteLocallyConstantAddCommGrp G) (colimit F)) :
      IsFiltered.IsEssentiallyConstant F ∧
      Nonempty (Ind.yoneda.obj (colimit F) ≅ (Ind.lim I).obj F) := sorry

end IsConstructibleEtaleAddCommGrp

namespace IsConstructibleEtaleModule

/-- A filtered colimit of constructible module-valued étale sheaves over a Noetherian ring with
constructible colimit is essentially constant, with the colimit sheaf as its value in the
ind-category. -/

theorem indObject_isEssentiallyConstant
    {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
      (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    {I : Type (max (u + 1) w)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)) [HasColimit F]
    (h_obj : ∀ i,
      IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
          IsFiniteTypeLocallyConstantModule G) (F.obj i))
    (h_colim :
      IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
          IsFiniteTypeLocallyConstantModule G) (colimit F)) :
      IsFiltered.IsEssentiallyConstant F ∧
      Nonempty (Ind.yoneda.obj (colimit F) ≅ (Ind.lim I).obj F) := sorry

end IsConstructibleEtaleModule

end CategoryTheory.Sheaf
