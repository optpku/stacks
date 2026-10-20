/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.PresheafFiber.Map
public import ReasLib.CategoryTheory.Sites.Point.EssentiallySmallFiber.PresheafFiber
public import ReasLib.CategoryTheory.Sites.Point.Reindexing.EssentiallySmall

/-!
# Presheaf-fiber maps for reindexed inverse systems

Fiber reindexing induces maps on raw presheaf fibers.  The cofiltered
specialization derives the required element-category colimits internally.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q w₀ w₁ w₂ v₀ v₁ v₂

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.Reindexing

namespace EssentiallySmall

variable {C : Type u} [Category.{v} C]
variable {I : Type w₀} [Category.{v₀} I]
variable {I' : Type w₁} [Category.{v₁} I']
variable {S : Iᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} Iᵒᵖ] [EssentiallySmall.{q} I'ᵒᵖ]

/-- The map on raw presheaf fibers induced by an essentially-small reindexing.
The source and target element-category colimits are explicit because they are
the minimal data used by `NatTrans.presheafFiber`. -/
noncomputable def presheafFiber
    (j : I ⥤ I') (T : I'ᵒᵖ ⥤ C) (e : S ≅ j.op ⋙ T)
    [HasColimitsOfShape
      (EssentiallySmallFiber.fiber S).Elementsᵒᵖ
      (Type q)]
    [HasColimitsOfShape
      (EssentiallySmallFiber.fiber T).Elementsᵒᵖ
      (Type q)] :
    EssentiallySmallFiber.presheafFiber S ⟶ EssentiallySmallFiber.presheafFiber T :=
  (fiber j T e).presheafFiber

section Naturality

variable {T : I'ᵒᵖ ⥤ C}
variable [HasColimitsOfShape
  (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable [HasColimitsOfShape
  (EssentiallySmallFiber.fiber T).Elementsᵒᵖ (Type q)]

/-- The generic reindexing map on presheaf fibers commutes with the canonical
maps from stagewise sections. -/
@[simp, reassoc]
theorem toPresheafFiber_naturality
    (j : I ⥤ I') (e : S ≅ j.op ⋙ T) (F : Cᵒᵖ ⥤ Type q)
    (X : C) (x : (EssentiallySmallFiber.fiber S).obj X) :
    EssentiallySmallFiber.toPresheafFiber S X x F ≫
        (presheafFiber j T e).app F =
      EssentiallySmallFiber.toPresheafFiber T X
        ((fiber j T e).app X x) F := sorry

end Naturality

/-- The presheaf-fiber map of the identity reindexing is the identity. -/
@[simp]
theorem presheafFiber_id (S : Iᵒᵖ ⥤ C)
    [HasColimitsOfShape
      (EssentiallySmallFiber.fiber S).Elementsᵒᵖ
      (Type q)] :
    presheafFiber (𝟭 I) S (idIso S) = 𝟙 (EssentiallySmallFiber.presheafFiber S) := sorry

section Composition

variable {I'' : Type w₂} [Category.{v₂} I'']
variable [EssentiallySmall.{q} I''ᵒᵖ]
variable {T : I'ᵒᵖ ⥤ C} {U : I''ᵒᵖ ⥤ C}

/-- Presheaf-fiber maps of successive essentially-small reindexings compose
to the map of their composite. -/
@[simp]
theorem presheafFiber_comp
    (j : I ⥤ I') (k : I' ⥤ I'') (e : S ≅ j.op ⋙ T) (e' : T ≅ k.op ⋙ U)
    [HasColimitsOfShape
      (EssentiallySmallFiber.fiber S).Elementsᵒᵖ
      (Type q)]
    [HasColimitsOfShape
      (EssentiallySmallFiber.fiber T).Elementsᵒᵖ
      (Type q)]
    [HasColimitsOfShape
      (EssentiallySmallFiber.fiber U).Elementsᵒᵖ
      (Type q)] :
    presheafFiber (j ⋙ k) U (compIso j k e e') =
      presheafFiber j T e ≫ presheafFiber k U e' := sorry

end Composition

namespace Cofiltered

variable [IsCofiltered Iᵒᵖ] [IsCofiltered I'ᵒᵖ]

/-- The map on raw presheaf fibers of essentially-small cofiltered inverse
systems. This convenience owner derives both element-category colimit
instances internally. -/
noncomputable abbrev presheafFiber
    (j : I ⥤ I') (T : I'ᵒᵖ ⥤ C) (e : S ≅ j.op ⋙ T) :
    EssentiallySmallFiber.Cofiltered.presheafFiber S ⟶
      EssentiallySmallFiber.Cofiltered.presheafFiber T :=
  letI : InitiallySmall.{q} Iᵒᵖ := initiallySmall_of_essentiallySmall Iᵒᵖ
  letI : InitiallySmall.{q} I'ᵒᵖ := initiallySmall_of_essentiallySmall I'ᵒᵖ
  letI : HasColimitsOfShape
      (EssentiallySmallFiber.fiber S).Elementsᵒᵖ
      (Type q) :=
    hasColimitsOfShape_of_finallySmall _ _
  letI : HasColimitsOfShape
      (EssentiallySmallFiber.fiber T).Elementsᵒᵖ
      (Type q) :=
    hasColimitsOfShape_of_finallySmall _ _
  Reindexing.EssentiallySmall.presheafFiber j T e

/-- The cofiltered presheaf-fiber map of the identity reindexing is the identity. -/
@[simp]
theorem presheafFiber.id (S : Iᵒᵖ ⥤ C) :
    presheafFiber (𝟭 I) S (idIso S) =
      𝟙 (EssentiallySmallFiber.Cofiltered.presheafFiber S) := sorry

section Composition

variable {I'' : Type w₂} [Category.{v₂} I'']
variable [EssentiallySmall.{q} I''ᵒᵖ] [IsCofiltered I''ᵒᵖ]
variable {T : I'ᵒᵖ ⥤ C} {U : I''ᵒᵖ ⥤ C}

/-- Cofiltered presheaf-fiber maps of successive reindexings compose to the
map of their composite. -/
@[simp]
theorem presheafFiber.comp
    (j : I ⥤ I') (k : I' ⥤ I'') (e : S ≅ j.op ⋙ T) (e' : T ≅ k.op ⋙ U) :
    presheafFiber (j ⋙ k) U (compIso j k e e') =
      presheafFiber j T e ≫ presheafFiber k U e' := sorry

end Composition

/-- The cofiltered reindexing map on presheaf fibers commutes with canonical
germ maps. -/
@[simp, reassoc]
theorem toPresheafFiber_naturality
    (j : I ⥤ I') (e : S ≅ j.op ⋙ T) (F : Cᵒᵖ ⥤ Type q)
    (X : C) (x : (EssentiallySmallFiber.fiber S).obj X) :
    EssentiallySmallFiber.Cofiltered.toPresheafFiber S X x F ≫
        (presheafFiber j T e).app F =
      EssentiallySmallFiber.Cofiltered.toPresheafFiber T X
        ((fiber j T e).app X x) F := sorry

end Cofiltered

end EssentiallySmall

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.Reindexing
