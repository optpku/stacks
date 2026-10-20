/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Products
public import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.CrossRefAttribute

/-!
# Positive finite powers

This file records the exact objectwise existence condition for the nonempty finite powers of one
object.  It is weaker than finite products in the ambient category and avoids exposing a dependent
family of `HasProduct` instances at every use site.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- `HasPositivePowers X` records the products of every nonempty finite constant family at `X`.
It does not require a terminal object or products involving unrelated objects. -/
@[stacks 0182 "positive finite powers of an object"]
class HasPositivePowers (X : C) : Prop where
  /-- The `(n + 1)`-fold power of `X` exists. -/
  hasProduct (n : ℕ) : HasProduct (fun _ : Fin (n + 1) ↦ X)

attribute [instance 50] HasPositivePowers.hasProduct

namespace HasPositivePowers

/-- An equivalence with `Fin n` for a nonempty type may be viewed as an equivalence with the
definitionally positive ordinal `Fin (n.pred + 1)`. -/
@[stacks 0182 "positive finite indexing normalization"]
noncomputable def equivFinPredSucc {ι : Type w} [Nonempty ι] {n : ℕ}
    (e : ι ≃ Fin n) : ι ≃ Fin (n.pred + 1) :=
  match n with
  | 0 => nomatch e (Classical.choice (inferInstance : Nonempty ι))
  | _ + 1 => e

/-- Reindex a nonempty finite type by a positive finite ordinal.  The predecessor in the target
only records the positivity forced by `Nonempty ι`; the equivalence itself comes from the
canonical finite-cardinality model. -/
@[stacks 0182 "positive finite indexing equivalence"]
noncomputable def indexEquiv (ι : Type w) [Finite ι] [Nonempty ι] :
    ι ≃ Fin ((Nat.card ι).pred + 1) :=
  equivFinPredSucc (Finite.equivFin ι)

/-- Positive powers provide a constant product indexed by any nonempty finite type.  This
low-priority bridge leaves ambient finite-product instances as the preferred search path. -/
@[stacks 0182 "positive power indexed by a finite nonempty type"]
noncomputable instance (priority := 25) hasProductOfFinite (X : C)
    [HasPositivePowers X] (ι : Type w) [Finite ι] [Nonempty ι] :
    HasProduct (fun _ : ι ↦ X) :=
  hasProduct_of_equiv_of_iso
    (fun _ : Fin ((Nat.card ι).pred + 1) ↦ X) (fun _ : ι ↦ X)
      (indexEquiv ι) (fun _ ↦ Iso.refl X)

/-- Binary products supply all positive finite powers of every object. -/
@[stacks 0182 "positive powers from binary products"]
instance ofHasBinaryProducts (X : C) [HasBinaryProducts C] : HasPositivePowers X :=
  ⟨fun n ↦ FiniteNonempty.hasProductFinSucc C n (fun _ ↦ X)⟩

end HasPositivePowers

end CategoryTheory.Limits
