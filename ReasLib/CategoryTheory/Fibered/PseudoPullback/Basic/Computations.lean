/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Construction

/-!
# Computation API for explicit pseudo-pullbacks

This leaf owns the constructor, projection, identity, composition, and lifting formulas for the
explicit pseudo-pullback. It deliberately depends only on the construction leaf, making it the
smallest general-purpose import for downstream objectwise and morphismwise calculations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor

universe u v w vB uX vX uY vY uS vS

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}

namespace PseudoPullback

/-- The common base of an explicitly constructed pseudo-pullback object is the supplied base
object. -/
@[simp]
theorem mk.baseObj
    (U : C) (P : CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)) :
    baseObj (mk F G U P) = U := sorry

/-- The fibrewise object of an explicitly constructed pseudo-pullback object is the supplied
categorical-pullback object. -/
@[simp]
theorem mk.fiberObj
    (U : C) (P : CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)) :
    fiberObj (mk F G U P) = P := sorry

/-- Reconstructing a pseudo-pullback object from its public base and fibrewise object is the
identity. This is the public eta rule for `PseudoPullback.mk`. -/
@[simp]
theorem mk.eta (P : (PseudoPullback F G).obj) :
    mk F G (PseudoPullback.baseObj P) (PseudoPullback.fiberObj P) = P := sorry

/-- The first component of an explicitly constructed pseudo-pullback object is the supplied
first fibre component. -/
@[simp]
theorem mk.fstObj
    (U : C) (P : CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)) :
    fstObj (mk F G U P) = P.fst.1 := sorry

/-- The second component of an explicitly constructed pseudo-pullback object is the supplied
second fibre component. -/
@[simp]
theorem mk.sndObj
    (U : C) (P : CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)) :
    sndObj (mk F G U P) = P.snd.1 := sorry

/-- The first stored base identification of an explicitly constructed pseudo-pullback object is
the equality transport supplied by its fibrewise first component. -/
@[simp]
theorem mk.fstBaseIso
    (U : C) (P : CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)) :
    fstBaseIso (mk F G U P) = eqToIso P.fst.2 := sorry

/-- The second stored base identification of an explicitly constructed pseudo-pullback object is
the equality transport supplied by its fibrewise second component. -/
@[simp]
theorem mk.sndBaseIso
    (U : C) (P : CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)) :
    sndBaseIso (mk F G U P) = eqToIso P.snd.2 := sorry

/-- The objectwise comparison of an explicitly constructed pseudo-pullback object is the
ambient image of its supplied fibrewise comparison. -/
@[simp]
theorem mk.comparisonIsoApp
    (U : C) (P : CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)) :
    comparisonIsoApp (mk F G U P) =
      (fiberInclusion : S.p.Fiber U ⥤ S.obj).mapIso P.iso := sorry

/-- The comparison morphism of an explicitly constructed pseudo-pullback object is the
underlying forward map of its supplied fibrewise comparison. -/
@[simp]
theorem mk.comparison
    (U : C) (P : CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)) :
    comparison (mk F G U P) = P.iso.hom.1 := sorry

/-- The forward map of the objectwise comparison isomorphism is the public comparison
morphism. -/
@[simp]
theorem comparisonIsoApp.hom (P : (PseudoPullback F G).obj) :
    (comparisonIsoApp P).hom = comparison P := sorry

/-- The forward map of the objectwise comparison isomorphism is vertical over the common base
object. This is the isomorphism-facing form of `comparison.isHomLift`. -/
theorem comparisonIsoApp.hom.isHomLift (P : (PseudoPullback F G).obj) :
    S.p.IsHomLift (𝟙 (baseObj P)) (comparisonIsoApp P).hom := sorry

/-- The inverse map of the objectwise comparison isomorphism is vertical over the common base
object. Together with `comparisonIsoApp.hom.isHomLift`, this permits direct use of the comparison
as an isomorphism in the standard fibre. -/
theorem comparisonIsoApp.inv.isHomLift (P : (PseudoPullback F G).obj) :
    S.p.IsHomLift (𝟙 (baseObj P)) (comparisonIsoApp P).inv := sorry

/-- The comparison morphism lies over the identity of the common base object. -/
instance comparison.isHomLift (P : (PseudoPullback F G).obj) :
    S.p.IsHomLift (𝟙 (baseObj P)) (comparison P) := sorry
-- Proof strategy: coerce P to the private object carrier and use its internal lift instance.

/-- The common base map of an explicitly constructed pseudo-pullback morphism is the supplied
base map. -/
@[simp]
theorem Hom.mk.baseMap
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ⟶ baseObj Q)
    (fst : fstObj P ⟶ fstObj Q) (fst_isHomLift : X.p.IsHomLift base fst)
    (snd : sndObj P ⟶ sndObj Q) (snd_isHomLift : Y.p.IsHomLift base snd)
    (comm : CommSq (F.toFunctor.map fst) (comparison P) (comparison Q)
      (G.toFunctor.map snd)) :
    baseMap (PseudoPullback.Hom.mk
      base fst fst_isHomLift snd snd_isHomLift comm) =
      base := sorry

/-- The common base map of a typeclass-constructed pseudo-pullback morphism is the supplied
base map. -/
@[simp]
theorem homMk.baseMap
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ⟶ baseObj Q)
    (fst : fstObj P ⟶ fstObj Q) [fst_isHomLift : X.p.IsHomLift base fst]
    (snd : sndObj P ⟶ sndObj Q) [snd_isHomLift : Y.p.IsHomLift base snd]
    (comm : CommSq (F.toFunctor.map fst) (comparison P) (comparison Q)
      (G.toFunctor.map snd)) :
    baseMap (homMk base fst snd comm) = base := sorry

/-- The common base-map view sends identity morphisms to identity morphisms. -/
@[simp]
theorem baseMap.id (P : (PseudoPullback F G).obj) :
    baseMap (𝟙 P) = 𝟙 (baseObj P) := sorry

/-- The common base-map view sends composition to composition. -/
@[simp]
theorem baseMap.comp {P Q R : (PseudoPullback F G).obj} (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    baseMap (φ ≫ ψ) = baseMap φ ≫ baseMap ψ := sorry

/-- The bundled projection sends a pseudo-pullback object to its common base object. -/
@[simp]
theorem p.obj (P : (PseudoPullback F G).obj) :
    (PseudoPullback F G).p.obj P = baseObj P := sorry
-- Proof strategy: unfold PseudoPullback, its baseFunctor, and baseObj.

/-- The bundled projection sends a pseudo-pullback morphism to its common base map. -/
@[simp]
theorem p.map {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    (PseudoPullback F G).p.map φ = baseMap φ := sorry
-- Proof strategy: unfold PseudoPullback, its baseFunctor, and baseMap.

/-- The first component of an explicitly constructed pseudo-pullback morphism is the supplied
first component. -/
@[simp]
theorem Hom.mk.fstMap
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ⟶ baseObj Q)
    (fst : fstObj P ⟶ fstObj Q) (fst_isHomLift : X.p.IsHomLift base fst)
    (snd : sndObj P ⟶ sndObj Q) (snd_isHomLift : Y.p.IsHomLift base snd)
    (comm : CommSq (F.toFunctor.map fst) (comparison P) (comparison Q)
      (G.toFunctor.map snd)) :
    fstMap (PseudoPullback.Hom.mk
      base fst fst_isHomLift snd snd_isHomLift comm) =
      fst := sorry

/-- The first component of a typeclass-constructed pseudo-pullback morphism is the supplied
first component. -/
@[simp]
theorem homMk.fstMap
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ⟶ baseObj Q)
    (fst : fstObj P ⟶ fstObj Q) [fst_isHomLift : X.p.IsHomLift base fst]
    (snd : sndObj P ⟶ sndObj Q) [snd_isHomLift : Y.p.IsHomLift base snd]
    (comm : CommSq (F.toFunctor.map fst) (comparison P) (comparison Q)
      (G.toFunctor.map snd)) :
    fstMap (homMk base fst snd comm) = fst := sorry

/-- The second component of an explicitly constructed pseudo-pullback morphism is the supplied
second component. -/
@[simp]
theorem Hom.mk.sndMap
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ⟶ baseObj Q)
    (fst : fstObj P ⟶ fstObj Q) (fst_isHomLift : X.p.IsHomLift base fst)
    (snd : sndObj P ⟶ sndObj Q) (snd_isHomLift : Y.p.IsHomLift base snd)
    (comm : CommSq (F.toFunctor.map fst) (comparison P) (comparison Q)
      (G.toFunctor.map snd)) :
    sndMap (PseudoPullback.Hom.mk
      base fst fst_isHomLift snd snd_isHomLift comm) =
      snd := sorry

/-- The second component of a typeclass-constructed pseudo-pullback morphism is the supplied
second component. -/
@[simp]
theorem homMk.sndMap
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ⟶ baseObj Q)
    (fst : fstObj P ⟶ fstObj Q) [fst_isHomLift : X.p.IsHomLift base fst]
    (snd : sndObj P ⟶ sndObj Q) [snd_isHomLift : Y.p.IsHomLift base snd]
    (comm : CommSq (F.toFunctor.map fst) (comparison P) (comparison Q)
      (G.toFunctor.map snd)) :
    sndMap (homMk base fst snd comm) = snd := sorry

/-- The first component view sends an identity pseudo-pullback morphism to an identity. -/
@[simp]
theorem fstMap.id (P : (PseudoPullback F G).obj) :
    fstMap (𝟙 P) = 𝟙 (fstObj P) := sorry
/- Proof strategy: unfold the public views and use the implementation identity law; the resulting
component equality is definitionally `rfl`. -/

/-- The first component view sends composition to composition. -/
@[simp]
theorem fstMap.comp {P Q R : (PseudoPullback F G).obj} (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    fstMap (φ ≫ ψ) = fstMap φ ≫ fstMap ψ := sorry
/- Proof strategy: unfold the public views and use the implementation composition law; the
resulting component equality is definitionally `rfl`. -/

/-- The second component view sends an identity pseudo-pullback morphism to an identity. -/
@[simp]
theorem sndMap.id (P : (PseudoPullback F G).obj) :
    sndMap (𝟙 P) = 𝟙 (sndObj P) := sorry
/- Proof strategy: unfold the public views and use the implementation identity law; the resulting
component equality is definitionally `rfl`. -/

/-- The second component view sends composition to composition. -/
@[simp]
theorem sndMap.comp {P Q R : (PseudoPullback F G).obj} (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    sndMap (φ ≫ ψ) = sndMap φ ≫ sndMap ψ := sorry
/- Proof strategy: unfold the public views and use the implementation composition law; the
resulting component equality is definitionally `rfl`. -/

/-- The first component of a pseudo-pullback morphism lies over its common base map. -/
instance fstMap.isHomLift {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    X.p.IsHomLift (baseMap φ) (fstMap φ) := sorry
-- Proof strategy: extract fst_isHomLift from the implementation morphism.

/-- The second component of a pseudo-pullback morphism lies over its common base map. -/
instance sndMap.isHomLift {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    Y.p.IsHomLift (baseMap φ) (sndMap φ) := sorry
-- Proof strategy: extract snd_isHomLift from the implementation morphism.

end PseudoPullback
end BasedCategory
end CategoryTheory
