module

public import stacks_project.Chap59.Definition_59_71_1
public import ReasLib.CategoryTheory.Ind.EssentiallyConstant
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- Lemma 59.71.8 (1): on a quasi-compact quasi-separated scheme, a filtered colimit of
constructible étale sheaves of sets that is itself constructible has essentially constant
ind-object, with value the colimit sheaf. -/
@[stacks 095P]
theorem IsConstructibleEtaleSet.indObject_isEssentiallyConstant
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (Type (u + 1)) →
        Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (Type (u + 1)) → Prop)
    (F : I ⥤ Sheaf X.smallEtaleTopology (Type (u + 1))) [HasColimit F]
    (h_obj : ∀ i, IsConstructibleEtaleSet restrict finiteLocallyConstant (F.obj i))
    (h_colim : IsConstructibleEtaleSet restrict finiteLocallyConstant (colimit F)) :
    IsFiltered.IsEssentiallyConstant F ∧
      Nonempty (Ind.yoneda.obj (colimit F) ≅ (Ind.lim I).obj F) := sorry

/-- Lemma 59.71.8 (2): on a quasi-compact quasi-separated scheme, a filtered colimit of
constructible étale abelian sheaves that is itself constructible has essentially constant
ind-object, with value the colimit sheaf. -/
@[stacks 095P]
theorem IsConstructibleEtaleAddCommGrp.indObject_isEssentiallyConstant
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} →
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [HasColimit F]
    (h_obj : ∀ i, IsConstructibleEtaleAddCommGrp restrict finiteLocallyConstant (F.obj i))
    (h_colim : IsConstructibleEtaleAddCommGrp restrict finiteLocallyConstant (colimit F)) :
    IsFiltered.IsEssentiallyConstant F ∧
      Nonempty (Ind.yoneda.obj (colimit F) ≅ (Ind.lim I).obj F) := sorry

/-- Lemma 59.71.8 (3): on a quasi-compact quasi-separated scheme, for a Noetherian ring `Λ`,
a filtered colimit of constructible étale sheaves of `Λ`-modules that is itself constructible
has essentially constant ind-object, with value the colimit sheaf. -/
@[stacks 095P]
theorem IsConstructibleEtaleModule.indObject_isEssentiallyConstant
    {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    {I : Type (max (u + 1) w)} [SmallCategory I] [IsFiltered I]
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ) →
        Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ) → Prop)
    (F : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)) [HasColimit F]
    (h_obj : ∀ i, IsConstructibleEtaleModule restrict finiteTypeLocallyConstant (F.obj i))
    (h_colim : IsConstructibleEtaleModule restrict finiteTypeLocallyConstant (colimit F)) :
    IsFiltered.IsEssentiallyConstant F ∧
      Nonempty (Ind.yoneda.obj (colimit F) ≅ (Ind.lim I).obj F) := sorry

end CategoryTheory.Sheaf
