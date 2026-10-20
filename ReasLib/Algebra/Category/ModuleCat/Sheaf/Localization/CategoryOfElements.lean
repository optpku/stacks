/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive
public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of module sheaves at a sheaf

This file owns restriction to the category-of-elements presentation of the
slice topos at a set-valued sheaf.  Its left adjoint is exposed both abstractly
and as presheaf pullback followed by module sheafification.  The presheaf-level
API records the canonical direct-sum map indexed by the sections of the
localizing sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w z

namespace PresheafOfModules.Localization.AtSheaf

variable {C : Type u} [Category.{v} C]
variable (R : Cᵒᵖ ⥤ RingCat.{w}) (F : Cᵒᵖ ⥤ Type v)

/-- The ring presheaf on the opposite category of elements of `F`. -/
abbrev ring : F.Elementsᵒᵖᵒᵖ ⥤ RingCat.{w} :=
  (CategoryTheory.Presheaf.elementsOpProjection F).op ⋙ R

/-- Restriction of module presheaves to the category of elements of `F`. -/
@[stacks 04IE "(2), presheaf restriction"]
noncomputable abbrev restriction :
    PresheafOfModules.{z} R ⥤ PresheafOfModules.{z} (ring R F) :=
  PresheafOfModules.pushforward (𝟙 (ring R F))

section LowerShriek

variable [(restriction R F).IsRightAdjoint]

/-- Lower shriek from the category of elements, defined as the left adjoint of restriction. -/
@[stacks 04IE "(4), presheaf lower shriek"]
noncomputable abbrev lowerShriek :
    PresheafOfModules.{z} (ring R F) ⥤ PresheafOfModules.{z} R :=
  (restriction R F).leftAdjoint

/-- Lower shriek is left adjoint to restriction to the category of elements. -/
noncomputable def lowerShriekRestrictionAdj :
    lowerShriek R F ⊣ restriction R F :=
  Adjunction.ofIsRightAdjoint (restriction R F)

/-- The object of the localization site determined by `s ∈ F(V)`. -/
abbrev sectionObject (V : C) (s : F.obj (op V)) : F.Elementsᵒᵖ :=
  op (Functor.elementsMk F (op V) s)

/-- The module fiber of `G` above a section `s ∈ F(V)`. -/
abbrev fiberModule
    (G : PresheafOfModules.{z} (ring R F)) (V : C) (s : F.obj (op V)) :
    ModuleCat.{z} (R.obj (op V)) :=
  G.obj (op (sectionObject F V s))

/-- The summand indexed by `s ∈ F(V)` maps canonically to lower shriek evaluated at `V`. -/
noncomputable def summandToLowerShriek
    (G : PresheafOfModules.{z} (ring R F)) (V : C) (s : F.obj (op V)) :
    fiberModule R F G V s ⟶
      ((lowerShriek R F).obj G).obj (op V) :=
  ((lowerShriekRestrictionAdj R F).unit.app G).app (op (sectionObject F V s))

/-- The canonical map from the direct sum over `s ∈ F(V)` to lower shriek at `V`. -/
@[stacks 04IE "(4), direct-sum map"]
noncomputable def coproductToLowerShriek
    (G : PresheafOfModules.{z} (ring R F)) (V : C)
    [HasCoproduct (fun s : F.obj (op V) ↦ fiberModule R F G V s)] :
    (∐ fun s : F.obj (op V) ↦ fiberModule R F G V s) ⟶
      ((lowerShriek R F).obj G).obj (op V) :=
  Sigma.desc (summandToLowerShriek R F G V)

/-- The direct sum over the fibers above sections of `F` computes presheaf lower shriek. -/
@[stacks 04IE "(4), direct-sum formula"]
theorem coproductToLowerShriek_isIso
    (G : PresheafOfModules.{z} (ring R F)) (V : C)
    [HasCoproduct (fun s : F.obj (op V) ↦ fiberModule R F G V s)] :
    IsIso (coproductToLowerShriek R F G V) := sorry

end LowerShriek

end PresheafOfModules.Localization.AtSheaf

namespace SheafOfModules.Localization.AtSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{w}) (F : Sheaf J (Type v))

/-- The ring sheaf on the category-of-elements presentation of the slice topos at `F`. -/
@[stacks 04IE "localized structure ring"]
abbrev ring : Sheaf (localizationTopology F) RingCat.{w} :=
  ((localizationProjection F).sheafPushforwardContinuous
    RingCat.{w} (localizationTopology F) J).obj R

/-- The identity structure-ring map underlying restriction to the localization at `F`. -/
@[stacks 04IE "(2), inverse-image structure map"]
abbrev restrictionRingHom :
    ring R F ⟶
      ((localizationProjection F).sheafPushforwardContinuous
        RingCat.{w} (localizationTopology F) J).obj R :=
  𝟙 (ring R F)

/-- Restriction of module sheaves to the category-of-elements localization at `F`. -/
@[stacks 04IE "(2), module inverse image"]
noncomputable abbrev restriction :
    SheafOfModules.{z} R ⥤ SheafOfModules.{z} (ring R F) :=
  SheafOfModules.pushforward (restrictionRingHom R F)

/-- Restriction to a category-of-elements localization is additive.  Naming this specialization
keeps downstream derived-functor instance search from unfolding the entire localization site. -/
instance restriction_additive :
    (restriction R F : SheafOfModules.{z} R ⥤
      SheafOfModules.{z} (ring R F)).Additive := sorry

section LowerShriek

variable [(restriction R F).IsRightAdjoint]

/-- Module lower shriek from the localization at `F`. -/
@[stacks 04IE "(4), module lower shriek"]
noncomputable abbrev lowerShriek :
    SheafOfModules.{z} (ring R F) ⥤ SheafOfModules.{z} R :=
  (restriction R F).leftAdjoint

/-- Module lower shriek is left adjoint to restriction at `F`. -/
noncomputable def lowerShriekRestrictionAdj :
    lowerShriek R F ⊣ restriction R F :=
  Adjunction.ofIsRightAdjoint (restriction R F)

/-- The Hom equivalence characterizing module lower shriek at `F`. -/
noncomputable def lowerShriekHomEquiv
    (G : SheafOfModules.{z} (ring R F)) (M : SheafOfModules.{z} R) :
    ((lowerShriek R F).obj G ⟶ M) ≃ (G ⟶ (restriction R F).obj M) :=
  (lowerShriekRestrictionAdj R F).homEquiv G M

end LowerShriek

section Construction

variable [presheafRestrictionIsRightAdjoint :
  ((PresheafOfModules.pushforward (restrictionRingHom R F).hom) :
    PresheafOfModules.{z} R.obj ⥤
      PresheafOfModules.{z} (ring R F).obj).IsRightAdjoint]

/-- The presheaf-module model of lower shriek before ambient sheafification. -/
@[stacks 04IE "(4), presheaf model"]
noncomputable abbrev lowerShriekPresheaf :
    SheafOfModules.{z} (ring R F) ⥤ PresheafOfModules.{z} R.obj :=
  SheafOfModules.forget (ring R F) ⋙
    PresheafOfModules.pullback (restrictionRingHom R F).hom

namespace LowerShriekPresheaf

/-- The module fiber of a localized module sheaf above `s ∈ F(V)`. -/
abbrev fiber (G : SheafOfModules.{z} (ring R F)) (V : C)
    (s : F.obj.obj (op V)) : ModuleCat.{z} (R.obj.obj (op V)) :=
  G.val.obj
    (op (PresheafOfModules.Localization.AtSheaf.sectionObject F.obj V s))

/-- The fiber above `s ∈ F(V)` maps canonically to the presheaf model of lower shriek at `V`. -/
noncomputable def summand (G : SheafOfModules.{z} (ring R F))
    (V : C) (s : F.obj.obj (op V)) :
    fiber R F G V s ⟶ ((lowerShriekPresheaf R F).obj G).obj (op V) :=
  ((Adjunction.ofIsRightAdjoint
    (PresheafOfModules.pushforward (restrictionRingHom R F).hom :
      PresheafOfModules.{z} R.obj ⥤
        PresheafOfModules.{z} (ring R F).obj)).unit.app G.val).app
      (op (PresheafOfModules.Localization.AtSheaf.sectionObject F.obj V s))

/-- The canonical direct-sum map computing the presheaf model of lower shriek at `V`. -/
@[stacks 04IE "(4), direct-sum map"]
noncomputable def coproductMap (G : SheafOfModules.{z} (ring R F)) (V : C)
    [HasCoproduct (fun s : F.obj.obj (op V) ↦ fiber R F G V s)] :
    (∐ fun s : F.obj.obj (op V) ↦ fiber R F G V s) ⟶
      ((lowerShriekPresheaf R F).obj G).obj (op V) :=
  Sigma.desc (summand R F G V)

/-- Before sheafification, lower shriek is the direct sum of the fibers indexed by
`s ∈ F(V)`. -/
@[stacks 04IE "(4), direct-sum formula"]
theorem coproductMap_isIso (G : SheafOfModules.{z} (ring R F)) (V : C)
    [HasCoproduct (fun s : F.obj.obj (op V) ↦ fiber R F G V s)] :
    IsIso (coproductMap R F G V) := sorry

end LowerShriekPresheaf

section Sheafification

variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]

/-- The explicit lower-shriek construction: presheaf lower shriek followed by sheafification. -/
@[stacks 04IE "(4), sheafification formula"]
noncomputable abbrev lowerShriekSheafification :
    SheafOfModules.{z} (ring R F) ⥤ SheafOfModules.{z} R :=
  lowerShriekPresheaf R F ⋙
    PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)

/-- The sheafified presheaf construction is left adjoint to restriction at `F`. -/
noncomputable def lowerShriekSheafificationAdj :
    lowerShriekSheafification R F ⊣ restriction R F :=
  @SheafOfModules.PullbackConstruction.adjunction _ _ _ _ _ _ _ _ _ _
    (restrictionRingHom R F) presheafRestrictionIsRightAdjoint _ _

/-- Standard sheafification hypotheses provide the canonical lower shriek at `F`. -/
noncomputable instance restrictionIsRightAdjoint :
    (restriction R F : SheafOfModules.{z} R ⥤
      SheafOfModules.{z} (ring R F)).IsRightAdjoint :=
  (lowerShriekSheafificationAdj R F).isRightAdjoint

/-- Abstract lower shriek agrees with the presheaf direct-sum construction followed by
sheafification. -/
@[stacks 04IE "(4), lower-shriek comparison"]
noncomputable def lowerShriekSheafificationIso :
    (lowerShriek R F : SheafOfModules.{z} (ring R F) ⥤
      SheafOfModules.{z} R) ≅ lowerShriekSheafification R F :=
  Adjunction.leftAdjointUniq (lowerShriekRestrictionAdj R F)
    (lowerShriekSheafificationAdj R F)

end Sheafification

end Construction

end SheafOfModules.Localization.AtSheaf
