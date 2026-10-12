/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Underlying
public import ReasLib.AlgebraicGeometry.RingedSite.Module.BaseChange
public import ReasLib.CategoryTheory.Sites.BeckChevalley
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module base change from squares of sites

The site-level Beck--Chevalley map is not automatically a morphism of module sheaves.  This leaf
records the missing mathematical datum explicitly: a square of module pullbacks together with the
statement that its mate becomes the site-level comparison after forgetting module structure.
Finality can then be transferred through the conservative forgetful functor.

This separation prevents a merely commutative square of underlying site functors from being used as
if it also contained the necessary compatibility of the four structure-ring maps.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ w z

namespace RingedSite.Hom.FinalSquare

section Definition

variable {X' : RingedSite.{u₀, v₀, w}} {X : RingedSite.{u₁, v₁, w}}
variable {Y' : RingedSite.{u₂, v₂, w}} {Y : RingedSite.{u₃, v₃, w}}
variable (g' : Hom X' X) (f' : Hom X' Y') (f : Hom X Y) (g : Hom Y' Y)
variable [(g'.modulePushforward.{z}).IsRightAdjoint]
variable [(f'.modulePushforward.{z}).IsRightAdjoint]
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [(g.modulePushforward.{z}).IsRightAdjoint]

variable (u' : X' ⥤ Y') (v' : X' ⥤ X) (u : X ⥤ Y) (v : Y' ⥤ Y)
variable [u.IsCocontinuous X.siteTopology Y.siteTopology]
variable [u'.IsCocontinuous X'.siteTopology Y'.siteTopology]
variable [v.IsContinuous Y'.siteTopology Y.siteTopology]
variable [v'.IsContinuous X'.siteTopology X.siteTopology]
variable [∀ F : X'ᵒᵖ ⥤ Type z, u'.op.HasPointwiseRightKanExtension F]
variable [∀ F : Xᵒᵖ ⥤ Type z, u.op.HasPointwiseRightKanExtension F]
variable [HasWeakSheafify X'.siteTopology (Type z)]
variable [HasWeakSheafify X.siteTopology (Type z)]

/-- A module-linear lift of the sheaf-level Beck--Chevalley comparison for a square of sites.
The two comparison isomorphisms encode the realization of the ringed-topos functors on underlying
sheaves, while `comparison_eq` is precisely the structure-ring linearity coherence absent from a
bare `CatCommSq`. -/
@[stacks 0FN3 "module-linear site lift"]
structure ModuleLift (sq : CatCommSq v' u' u v) where
  /-- The square of module pullback functors whose mate is the module comparison. -/
  pullbackSquare :
    TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z}
  /-- Identification of the underlying source composite with the source of the site comparison. -/
  sourceIso :
    (f.modulePushforward.{z} ⋙ g.modulePullback.{z}) ⋙
        SheafOfModules.toTypeSheaf Y'.structureSheaf ≅
      SheafOfModules.toTypeSheaf X.structureSheaf ⋙
        u.sheafPushforwardCocontinuous (Type z)
          X.siteTopology Y.siteTopology ⋙
        v.sheafPushforwardContinuous (Type z)
          Y'.siteTopology Y.siteTopology
  /-- Identification of the underlying target composite with the target of the site comparison. -/
  targetIso :
    (g'.modulePullback.{z} ⋙ f'.modulePushforward.{z}) ⋙
        SheafOfModules.toTypeSheaf Y'.structureSheaf ≅
      SheafOfModules.toTypeSheaf X.structureSheaf ⋙
        v'.sheafPushforwardContinuous (Type z)
          X'.siteTopology X.siteTopology ⋙
        u'.sheafPushforwardCocontinuous (Type z)
          X'.siteTopology Y'.siteTopology
  /-- After forgetting module structure, the module comparison is the site comparison. -/
  comparison_eq :
    Functor.whiskerRight
        (RingedSite.Hom.BaseChange.comparison g' f' f g pullbackSquare)
        (SheafOfModules.toTypeSheaf Y'.structureSheaf) =
      sourceIso.hom ≫
        Functor.whiskerLeft (SheafOfModules.toTypeSheaf X.structureSheaf)
          (CatCommSq.BeckChevalley.comparison
            X'.siteTopology X.siteTopology Y'.siteTopology Y.siteTopology sq) ≫
        targetIso.inv

end Definition

namespace ModuleLift

variable {X' : RingedSite.{u₀, v₀, w}} {X : RingedSite.{u₁, v₁, w}}
variable {Y' : RingedSite.{u₂, v₂, w}} {Y : RingedSite.{u₃, v₃, w}}
variable {g' : Hom X' X} {f' : Hom X' Y'} {f : Hom X Y} {g : Hom Y' Y}
variable [(g'.modulePushforward.{z}).IsRightAdjoint]
variable [(f'.modulePushforward.{z}).IsRightAdjoint]
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [(g.modulePushforward.{z}).IsRightAdjoint]

variable {u' : X' ⥤ Y'} {v' : X' ⥤ X} {u : X ⥤ Y} {v : Y' ⥤ Y}
variable [u.IsCocontinuous X.siteTopology Y.siteTopology]
variable [u'.IsCocontinuous X'.siteTopology Y'.siteTopology]
variable [v.IsContinuous Y'.siteTopology Y.siteTopology]
variable [v'.IsContinuous X'.siteTopology X.siteTopology]
variable [∀ F : X'ᵒᵖ ⥤ Type z, u'.op.HasPointwiseRightKanExtension F]
variable [∀ F : Xᵒᵖ ⥤ Type z, u.op.HasPointwiseRightKanExtension F]
variable [HasWeakSheafify X'.siteTopology (Type z)]
variable [HasWeakSheafify X.siteTopology (Type z)]

/-- The module base-change map carried by a module-linear lift of a site square. -/
@[stacks 0FN3 "module comparison"]
noncomputable def comparison {sq : CatCommSq v' u' u v}
    (L : ModuleLift g' f' f g u' v' u v sq) :
    f.modulePushforward.{z} ⋙ g.modulePullback.{z} ⟶
      g'.modulePullback.{z} ⋙ f'.modulePushforward.{z} :=
  RingedSite.Hom.BaseChange.comparison g' f' f g L.pullbackSquare

/-- Lemma 18.41.3 (0FN3) (1): finality of the site square makes its canonical module-linear
comparison invertible. -/
@[stacks 0FN3 "(1)"]
theorem comparison_isIso_of_final
    [v.IsCocontinuous Y'.siteTopology Y.siteTopology]
    [v'.IsCocontinuous X'.siteTopology X.siteTopology]
    {sq : CatCommSq v' u' u v}
    (L : ModuleLift g' f' f g u' v' u v sq)
    (hfinal : ∀ V : Y',
      (TwoSquare.costructuredArrowRightwards sq.iso.hom V).Final) :
    IsIso L.comparison := sorry

section LowerShriek

variable [(g'.modulePullback.{z}).IsRightAdjoint]
variable [(g.modulePullback.{z}).IsRightAdjoint]

/-- The canonical lower-shriek mate carried by a module-linear lift of a site square. -/
@[stacks 0FN3 "lower-shriek comparison"]
noncomputable def lowerShriekComparison {sq : CatCommSq v' u' u v}
    (L : ModuleLift g' f' f g u' v' u v sq) :
    f'.modulePullback.{z} ⋙ g'.moduleLowerShriek ⟶
      g.moduleLowerShriek ⋙ f.modulePullback.{z} :=
  RingedSite.Hom.BaseChange.mate g' f' f g L.comparison

/-- Lemma 18.41.3 (0FN3) (2): finality makes the canonical lower-shriek comparison of a lifted
site square invertible. -/
@[stacks 0FN3 "(2)"]
theorem lowerShriekComparison_isIso_of_final
    [v.IsCocontinuous Y'.siteTopology Y.siteTopology]
    [v'.IsCocontinuous X'.siteTopology X.siteTopology]
    {sq : CatCommSq v' u' u v}
    (L : ModuleLift g' f' f g u' v' u v sq)
    (hfinal : ∀ V : Y',
      (TwoSquare.costructuredArrowRightwards sq.iso.hom V).Final) :
    IsIso L.lowerShriekComparison := sorry

end LowerShriek

end ModuleLift

end RingedSite.Hom.FinalSquare
