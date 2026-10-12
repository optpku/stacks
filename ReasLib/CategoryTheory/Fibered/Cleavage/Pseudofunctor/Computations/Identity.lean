/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Construction

@[expose] public section

/-!
# Identity comparison of the pseudofunctor associated to a cleavage

The bicategorical identity constraint is normalized to the intrinsic unit comparison of
reindexing, both as a natural isomorphism and componentwise.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor.Cleavage

variable {p : S ⥤ C} (χ : p.Cleavage)

/-- After forgetting the `Cat` wrapper, the base-facing identity comparison is the inverse
intrinsic unit comparison of the cleavage. -/
@[simp]
theorem toPseudofunctor.mapIdOp.toNatIso (U : C) :
    Cat.Hom.toNatIso (χ.toPseudofunctor.mapIdOp U) =
      (Reindex.idIso χ U).symm := sorry

/-- The hom component of the base-facing identity comparison is the inverse component of the
canonical cleavage unit comparison. -/
@[simp]
theorem toPseudofunctor.mapIdOp.hom.app (U : C) (x : Fiber p U) :
    (χ.toPseudofunctor.mapIdOp U).hom.toNatTrans.app x =
      (Reindex.idIsoApp χ U x).inv := sorry
/- Proof strategy: unfold `mapIdOp` and `toPseudofunctor`; the pseudofunctor constructor stores
`Reindex.idIso χ U` with reversed orientation as its identity comparison. -/

/-- The inverse component of the base-facing identity comparison is the forward component of the
canonical cleavage unit comparison. -/
@[simp]
theorem toPseudofunctor.mapIdOp.inv.app (U : C) (x : Fiber p U) :
    (χ.toPseudofunctor.mapIdOp U).inv.toNatTrans.app x =
      (Reindex.idIsoApp χ U x).hom := sorry
/- Proof strategy: use the same normalization as the hom component and take the inverse side of
the resulting natural isomorphism. -/

/-- After forgetting the `Cat` wrapper, mathlib's standard identity comparison is the inverse
intrinsic unit comparison of the cleavage. -/
@[simp]
theorem toPseudofunctor.mapId.toNatIso (U : C) :
    Cat.Hom.toNatIso
        (χ.toPseudofunctor.mapId (LocallyDiscrete.mk (Opposite.op U))) =
      (Reindex.idIso χ U).symm := sorry

/-- The hom component of mathlib's standard identity comparison is the inverse cleavage unit
component. This complements the base-facing `mapIdOp` computation. -/
@[simp]
theorem toPseudofunctor.mapId.hom.app (U : C) (x : Fiber p U) :
    (χ.toPseudofunctor.mapId (LocallyDiscrete.mk (Opposite.op U))).hom.toNatTrans.app x =
      (Reindex.idIsoApp χ U x).inv := sorry

/-- The inverse component of mathlib's standard identity comparison is the forward cleavage unit
component. -/
@[simp]
theorem toPseudofunctor.mapId.inv.app (U : C) (x : Fiber p U) :
    (χ.toPseudofunctor.mapId (LocallyDiscrete.mk (Opposite.op U))).inv.toNatTrans.app x =
      (Reindex.idIsoApp χ U x).hom := sorry

end Functor.Cleavage

end CategoryTheory
