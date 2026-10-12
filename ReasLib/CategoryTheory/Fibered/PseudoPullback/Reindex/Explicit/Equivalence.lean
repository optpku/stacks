/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Explicit.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Cartesian
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Comparison.Forward.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Projection.Forward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing equivalences for explicit pseudo-pullback fibers

This file organizes the comparison between actual reindexing in a fibred pseudo-pullback and
componentwise reindexing in its categorical-pullback fiber model. The reusable owner is
`Fiber.reindex`; the selected-cleavage facade is defined separately from that owner.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback CategoryTheory.Bicategory

universe u v uX uY uS vX vY vS

namespace CategoryTheory

namespace BasedCategory.PseudoPullback

open BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

namespace Fiber.reindex

/-- The source functor for the reindexing comparison: first reindex an actual fiber of the
fibred pseudo-pullback, then identify the resulting fiber with its categorical-pullback model.
It needs only the displayed pseudo-pullback cleavage, not a Cartesian structure on the cospan. -/
noncomputable def source
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    (χP : (PseudoPullback F G).p.Cleavage)
    {U V : C} (f : V ⟶ U) :
    Functor.Fiber (PseudoPullback F G).p U ⥤
      (F.fiberFunctor V) ⊡ (G.fiberFunctor V) :=
  χP.reindex f ⋙ Fiber.comparison F G V

/-- The target functor for the reindexing comparison: first identify an actual fiber with its
categorical-pullback model, then reindex componentwise in that model. Its three explicit
cleavages are exactly the data used to construct the componentwise reindexing functor. -/
noncomputable def target
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U) :
    Functor.Fiber (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U ⥤
      (F.fiberFunctor V) ⊡ (G.fiberFunctor V) :=
  (Fiber.comparison F.toBasedFunctor G.toBasedFunctor U) ⋙
    BasedCategory.PseudoPullback.reindex.explicit.functor F G χX χY χS f

/-- After identifying actual pseudo-pullback fibers with their categorical-pullback models,
source and target reindexing have canonically isomorphic first projections. -/
@[stacks 0040 "first projection of actual-to-modeled pseudo-pullback reindexing"]
noncomputable def fstIso
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U) :
    source F.toBasedFunctor G.toBasedFunctor χP f ⋙ π₁ (F.fiberFunctor V) (G.fiberFunctor V) ≅
      target F G χX χY χS f ⋙ π₁ (F.fiberFunctor V) (G.fiberFunctor V) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (χP.reindex f)
      (Fiber.comparison.fstIso F.toBasedFunctor G.toBasedFunctor V) ≪≫
    (CartesianBasedFunctor.Reindex.natIso
      (cartesianFst.ofCleavage F G χX χY) χP χX f).symm ≪≫
    Functor.isoWhiskerRight
      (Fiber.comparison.fstIso F.toBasedFunctor G.toBasedFunctor U).symm
      (χX.reindex f) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (Fiber.comparison F.toBasedFunctor G.toBasedFunctor U)
      (BasedCategory.PseudoPullback.reindex.explicit.fst.iso F G χX χY χS f).symm ≪≫
    (Functor.associator _ _ _).symm

/-- After identifying actual pseudo-pullback fibers with their categorical-pullback models,
source and target reindexing have canonically isomorphic second projections. -/
@[stacks 0040 "second projection of actual-to-modeled pseudo-pullback reindexing"]
noncomputable def sndIso
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U) :
    source F.toBasedFunctor G.toBasedFunctor χP f ⋙ π₂ (F.fiberFunctor V) (G.fiberFunctor V) ≅
      target F G χX χY χS f ⋙ π₂ (F.fiberFunctor V) (G.fiberFunctor V) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (χP.reindex f)
      (Fiber.comparison.sndIso F.toBasedFunctor G.toBasedFunctor V) ≪≫
    (CartesianBasedFunctor.Reindex.natIso
      (cartesianSnd.ofCleavage F G χX χY) χP χY f).symm ≪≫
    Functor.isoWhiskerRight
      (Fiber.comparison.sndIso F.toBasedFunctor G.toBasedFunctor U).symm
      (χY.reindex f) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (Fiber.comparison F.toBasedFunctor G.toBasedFunctor U)
      (BasedCategory.PseudoPullback.reindex.explicit.snd.iso F G χX χY χS f).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The first- and second-projection comparisons are compatible with the structural
isomorphism of the categorical-pullback model. -/
theorem coherence
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U) :
    Functor.whiskerRight (fstIso F G χP χX χY χS f).hom
        (F.fiberFunctor V) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (target F G χX χY χS f)
          (CatCommSq.iso
            (π₁ (F.fiberFunctor V) (G.fiberFunctor V))
            (π₂ (F.fiberFunctor V) (G.fiberFunctor V))
            (F.fiberFunctor V) (G.fiberFunctor V)).hom ≫
        (Functor.associator _ _ _).inv =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (source F.toBasedFunctor G.toBasedFunctor χP f)
          (CatCommSq.iso
            (π₁ (F.fiberFunctor V) (G.fiberFunctor V))
            (π₂ (F.fiberFunctor V) (G.fiberFunctor V))
            (F.fiberFunctor V) (G.fiberFunctor V)).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (sndIso F G χP χX χY χS f).hom
          (G.fiberFunctor V) := sorry

/-- The naturality isomorphism identifying actual pseudo-pullback reindexing with
componentwise reindexing in its categorical-pullback fiber model. -/
@[stacks 0040 "actual-to-modeled pseudo-pullback fiber reindexing comparison"]
noncomputable def iso
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U) :
    source F.toBasedFunctor G.toBasedFunctor χP f ≅ target F G χX χY χS f :=
  CategoricalPullback.mkNatIso
    (fstIso F G χP χX χY χS f)
    (sndIso F G χP χX χY χS f)
    (coherence F G χP χX χY χS f)

namespace iso

/-- The first component of the forward source-to-target reindexing comparison. -/
@[simp]
theorem hom.fst
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    (P : Functor.Fiber
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U) :
    ((iso F G χP χX χY χS f).hom.app P).fst =
      (fstIso F G χP χX χY χS f).hom.app P := sorry

/-- The second component of the forward source-to-target reindexing comparison. -/
@[simp]
theorem hom.snd
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    (P : Functor.Fiber
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U) :
    ((iso F G χP χX χY χS f).hom.app P).snd =
      (sndIso F G χP χX χY χS f).hom.app P := sorry

/-- The first component of the inverse target-to-source reindexing comparison. -/
@[simp]
theorem inv.fst
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    (P : Functor.Fiber
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U) :
    ((iso F G χP χX χY χS f).inv.app P).fst =
      (fstIso F G χP χX χY χS f).inv.app P := sorry

/-- The second component of the inverse target-to-source reindexing comparison. -/
@[simp]
theorem inv.snd
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    (P : Functor.Fiber
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U) :
    ((iso F G χP χX χY χS f).inv.app P).snd =
      (sndIso F G χP χX χY χS f).inv.app P := sorry

/-- Compatibility of the forward reindexing comparison with composition of base arrows. -/
theorem mapComp.hom
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : Functor.Fiber
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U) :
    (iso F G χP χX χY χS (g ≫ f)).hom.app P ≫
        (BasedCategory.PseudoPullback.reindex.explicit.mapCompIso F G χX χY χS f g).hom.app
          ((Fiber.comparison F.toBasedFunctor G.toBasedFunctor U).obj P) =
      (Fiber.comparison F.toBasedFunctor G.toBasedFunctor W).map
          (Functor.Cleavage.Reindex.compIsoApp χP f g P).hom ≫
        (iso F G χP χX χY χS g).hom.app ((χP.reindex f).obj P) ≫
        (BasedCategory.PseudoPullback.reindex.explicit.functor F G χX χY χS g).map
          ((iso F G χP χX χY χS f).hom.app P) := sorry

/-- Compatibility of the inverse reindexing comparison with composition of base arrows. -/
theorem mapComp.inv
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : Functor.Fiber
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U) :
    (BasedCategory.PseudoPullback.reindex.explicit.mapCompIso F G χX χY χS f g).inv.app
          ((Fiber.comparison F.toBasedFunctor G.toBasedFunctor U).obj P) ≫
        (iso F G χP χX χY χS (g ≫ f)).inv.app P =
      (BasedCategory.PseudoPullback.reindex.explicit.functor F G χX χY χS g).map
          ((iso F G χP χX χY χS f).inv.app P) ≫
        (iso F G χP χX χY χS g).inv.app ((χP.reindex f).obj P) ≫
        (Fiber.comparison F.toBasedFunctor G.toBasedFunctor W).map
          (Functor.Cleavage.Reindex.compIsoApp χP f g P).inv := sorry

/-- Compatibility of the forward reindexing comparison with identity reindexing. -/
theorem mapId.hom
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U : C}
    (P : Functor.Fiber
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U) :
    (Fiber.comparison F.toBasedFunctor G.toBasedFunctor U).map
          (Functor.Cleavage.Reindex.idIsoApp χP U P).hom ≫
        (iso F G χP χX χY χS (𝟙 U)).hom.app P =
      (BasedCategory.PseudoPullback.reindex.explicit.idIso F G χX χY χS U).hom.app
        ((Fiber.comparison F.toBasedFunctor G.toBasedFunctor U).obj P) := sorry

/-- Compatibility of the inverse reindexing comparison with identity reindexing. -/
theorem mapId.inv
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U : C}
    (P : Functor.Fiber
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U) :
    (BasedCategory.PseudoPullback.reindex.explicit.idIso F G χX χY χS U).inv.app
          ((Fiber.comparison F.toBasedFunctor G.toBasedFunctor U).obj P) =
      (iso F G χP χX χY χS (𝟙 U)).inv.app P ≫
        (Fiber.comparison F.toBasedFunctor G.toBasedFunctor U).map
          (Functor.Cleavage.Reindex.idIsoApp χP U P).inv := sorry

end iso

end Fiber.reindex

end BasedCategory.PseudoPullback

end CategoryTheory
