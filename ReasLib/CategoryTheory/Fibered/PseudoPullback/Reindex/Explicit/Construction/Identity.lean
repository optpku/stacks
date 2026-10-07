module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Explicit.Construction.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Reindex.Identity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity Comparison for Explicit Fiber-Pullback Reindexing

This leaf owns the objectwise and natural identity comparisons for explicit-cleavage reindexing
of categorical pullbacks of fibers.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor
open scoped CategoricalPullback CategoryTheory.Bicategory

universe u v uX uY uS vX vY vS

namespace CategoryTheory

namespace BasedCategory.PseudoPullback.reindex.explicit

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

/-- The objectwise unit comparison from a fiber-pullback object to its reindexing along the
identity base arrow. -/
noncomputable def idIsoApp
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    P ≅ (functor F G χX χY χS (𝟙 U)).obj P :=
  (Pullback.Reindex.mapIdIsoApp
    (CartesianBasedFunctor.Indexed.explicit.functor F χX χS)
    (CartesianBasedFunctor.Indexed.explicit.functor G χY χS) U P).symm

/-- The left component of the forward objectwise unit comparison. -/
@[simp]
theorem idIsoApp.hom.fst
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (idIsoApp F G χX χY χS U P).hom.fst =
      (Functor.Cleavage.Reindex.idIsoApp χX U P.fst).hom := sorry

/-- The right component of the forward objectwise unit comparison. -/
@[simp]
theorem idIsoApp.hom.snd
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (idIsoApp F G χX χY χS U P).hom.snd =
      (Functor.Cleavage.Reindex.idIsoApp χY U P.snd).hom := sorry

/-- The left component of the inverse objectwise unit comparison. -/
@[simp]
theorem idIsoApp.inv.fst
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (idIsoApp F G χX χY χS U P).inv.fst =
      (Functor.Cleavage.Reindex.idIsoApp χX U P.fst).inv := sorry

/-- The right component of the inverse objectwise unit comparison. -/
@[simp]
theorem idIsoApp.inv.snd
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (idIsoApp F G χX χY χS U P).inv.snd =
      (Functor.Cleavage.Reindex.idIsoApp χY U P.snd).inv := sorry

/-- The objectwise unit comparisons for fiber-pullback reindexing are natural. -/
theorem idIsoApp.naturality.hom
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)} (φ : P ⟶ Q) :
    φ ≫ (idIsoApp F G χX χY χS U Q).hom =
      (idIsoApp F G χX χY χS U P).hom ≫
        (functor F G χX χY χS (𝟙 U)).map φ := sorry

/-- Inverse naturality of the objectwise unit comparison for fiber-pullback reindexing. -/
theorem idIsoApp.naturality.inv
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)} (φ : P ⟶ Q) :
    (functor F G χX χY χS (𝟙 U)).map φ ≫
        (idIsoApp F G χX χY χS U Q).inv =
      (idIsoApp F G χX χY χS U P).inv ≫ φ := sorry

/-- Identity reindexing of a categorical pullback of fibers is naturally isomorphic to the
identity functor. -/
@[stacks 0040 "explicit-cleavage identity comparison for fiber-pullback reindexing"]
noncomputable def idIso
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) :
    𝟭 ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)) ≅
      functor F G χX χY χS (𝟙 U) :=
  (Pullback.Reindex.mapIdIso
    (CartesianBasedFunctor.Indexed.explicit.functor F χX χS)
    (CartesianBasedFunctor.Indexed.explicit.functor G χY χS) U).symm

/-- The first component of the forward natural unit comparison is the cleavage unit comparison
in the left fiber. -/
@[simp]
theorem idIso.hom.app.fst
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    ((idIso F G χX χY χS U).hom.app P).fst =
      (Functor.Cleavage.Reindex.idIsoApp χX U P.fst).hom := sorry

/-- The second component of the forward natural unit comparison is the cleavage unit comparison
in the right fiber. -/
@[simp]
theorem idIso.hom.app.snd
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    ((idIso F G χX χY χS U).hom.app P).snd =
      (Functor.Cleavage.Reindex.idIsoApp χY U P.snd).hom := sorry

/-- The first component of the inverse natural unit comparison is the inverse cleavage unit
comparison in the left fiber. -/
@[simp]
theorem idIso.inv.app.fst
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    ((idIso F G χX χY χS U).inv.app P).fst =
      (Functor.Cleavage.Reindex.idIsoApp χX U P.fst).inv := sorry

/-- The second component of the inverse natural unit comparison is the inverse cleavage unit
comparison in the right fiber. -/
@[simp]
theorem idIso.inv.app.snd
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    ((idIso F G χX χY χS U).inv.app P).snd =
      (Functor.Cleavage.Reindex.idIsoApp χY U P.snd).inv := sorry

end BasedCategory.PseudoPullback.reindex.explicit

end CategoryTheory
