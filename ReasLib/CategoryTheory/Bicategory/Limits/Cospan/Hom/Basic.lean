/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic cospan transformation operations

`Cospan.Basic` is the neutral owner of the transformation type and its semantic vertex and
generating-cell projections. This leaf adds only the canonical identity and vertical composition
operations; constructors and their reduction laws are layered below it.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.CospanTransform

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' x'' y'' z'' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}
variable {f'' : x'' ⟶ z''} {g'' : y'' ⟶ z''}

/-- The identity strong transformation of a bicategorical cospan. -/
def id (f : x ⟶ z) (g : y ⟶ z) : CospanTransform f g f g :=
  Pseudofunctor.StrongTrans.id (cospan f g)

/-- Vertical composition of bicategorical cospan transformations. -/
def comp
    (ψ : CospanTransform f g f' g') (φ : CospanTransform f' g' f'' g'') :
    CospanTransform f g f'' g'' :=
  Pseudofunctor.StrongTrans.vcomp ψ φ

/- Data audit (mathlib 4.32): `id` and `comp` delegate to the canonical strong-transformation
operations. They introduce no new non-`Prop` choices; deferred coherence is inherited from the
ambient pseudofunctor API. -/

end CategoryTheory.Bicategory.CospanTransform
