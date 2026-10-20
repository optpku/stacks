/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.CategoryTheory.Limits.Colimit.Representable.Factorization

@[expose] public section

/-!
# Finite Initial Segments and Representable Colimits

This leaf packages the canonical sequential diagram of nonempty finite initial segments of `ℕ`,
its colimit calculation, and the resulting failure of `Hom(ℕ, -)` to preserve that colimit.
It is a reusable test object for compactness and presentability APIs.
-/

open CategoryTheory Opposite

namespace CategoryTheory.Limits.Types.FiniteInitialSegment

/-- The inclusion from one nonempty finite initial segment into the next. -/
def map (n : ℕ) : Fin (n + 1) ⟶ Fin (n + 2) :=
  ↾Fin.castSucc

/-- The sequential diagram of nonempty finite initial segments of `ℕ`. -/
@[stacks 05NP "finite-initial-segment diagram"]
def diagram : ℕ ⥤ Type :=
  Functor.ofSequence map

/-- The underlying-value map from the `n`th finite initial segment to `ℕ`. -/
def val (n : ℕ) : Fin (n + 1) ⟶ ℕ :=
  ↾fun i ↦ i.1

/-- The underlying-value maps commute with the successor inclusions. -/
theorem val_naturality (n : ℕ) :
    diagram.map (homOfLE (Nat.le_succ n)) ≫ val (n + 1) = val n := sorry

/-- The cocone of underlying-value maps from the finite initial segments to `ℕ`. -/
def natCocone : Cocone diagram where
  pt := ℕ
  ι := NatTrans.ofSequence val val_naturality

/-- The map from the sequential colimit to `ℕ` induced by underlying values. -/
noncomputable def toNat : colimit diagram ⟶ ℕ :=
  colimit.desc diagram natCocone

/-- The map from `ℕ` to the sequential colimit represented by the last point of each stage. -/
noncomputable def fromNat : ℕ ⟶ colimit diagram :=
  ↾fun n ↦ colimit.ι diagram n (Fin.last n)

/-- The colimit-to-`ℕ` map sends a stage representative to its underlying value. -/
theorem toNat_ι (n : ℕ) (i : Fin (n + 1)) :
    toNat (colimit.ι diagram n i) = i.1 := sorry

/-- Mapping a natural number into the colimit and back recovers that number. -/
theorem toNat_fromNat (n : ℕ) :
    toNat (fromNat n) = n := sorry

/-- Every colimit element is represented by the last point indexed by its underlying value. -/
theorem fromNat_toNat (x : colimit diagram) :
    fromNat (toNat x) = x := sorry

/-- Example 19.2.1 (05NP): the sequential colimit of the finite initial segments is canonically
equivalent to `ℕ`. -/
@[stacks 05NP "colimit of finite initial segments"]
noncomputable def colimitEquivNat : colimit diagram ≃ ℕ where
  toFun := toNat
  invFun := fromNat
  left_inv := fromNat_toNat
  right_inv := toNat_fromNat

/-- The canonical map `ℕ → colimit diagram` is different from every map that factors through
a prescribed finite stage. -/
theorem fromNat_ne_stage (m : ℕ) (f : ℕ ⟶ Fin (m + 1)) :
    fromNat ≠ f ≫ colimit.ι diagram m := sorry

/-- Example 19.2.1 (05NP): the canonical map from `ℕ` to that colimit does not factor through a
single finite stage. -/
@[stacks 05NP "no finite-stage factorization"]
theorem fromNat_not_factors :
    ¬ colimitPost.FactorsThroughStage diagram fromNat := sorry

/-- Example 19.2.1 (05NP): the representable-colimit comparison for `ℕ` and the sequential
diagram of finite initial segments is not surjective. -/
@[stacks 05NP "representable comparison not surjective"]
theorem comparison_not_surjective :
    ¬ Function.Surjective (colimit.post diagram (coyoneda.obj (op ℕ))) := sorry

end CategoryTheory.Limits.Types.FiniteInitialSegment
