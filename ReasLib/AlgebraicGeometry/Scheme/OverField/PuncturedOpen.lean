/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The open complement of the reduced closure of a point of a scheme over a field. -/
def puncturedOpen {k : Type u} [Field k] (C : SchemeOverField k) (Q : C.left) :
    C.left.Opens :=
  (Scheme.PointClosure.closedSubset Q).compl

/-- A point lies in `puncturedOpen C Q` if and only if it does not lie in the closure of `{Q}`. -/
theorem mem_puncturedOpen_iff {k : Type u} [Field k] (C : SchemeOverField k)
    (Q x : C.left) :
    x ∈ puncturedOpen C Q ↔ x ∉ closure ({Q} : Set C.left) := sorry

/-- If `Q` has residue degree `2` over the base field, then `{Q}` is closed and
`puncturedOpen C Q` is the complement of that singleton. -/
theorem puncturedOpen_eq_singleton_compl {k : Type u} [Field k] (C : SchemeOverField k)
    (Q : C.left) (hQ : C.hom.residueDegree Q = 2) :
    (puncturedOpen C Q : Set C.left) = ({Q} : Set C.left)ᶜ ∧
      IsClosed ({Q} : Set C.left) := sorry

/-- The product of the punctured opens `C i \ closure {Q i}`, realized as an open of `∏ᶜ C`. -/
def puncturedProductOpen {k : Type u} [Field k] {n : ℕ}
    (C : Fin n → SchemeOverField k) (Q : (i : Fin n) → (C i).left) :
    (∏ᶜ C).left.Opens :=
  ⨅ i, (Pi.π C i).left ⁻¹ᵁ puncturedOpen (C i) (Q i)

/-- A point of the product lies in `puncturedProductOpen C Q` if and only if none of its
coordinates lies in the corresponding singleton closure. -/
theorem mem_puncturedProductOpen_iff {k : Type u} [Field k] {n : ℕ}
    (C : Fin n → SchemeOverField k) (Q : (i : Fin n) → (C i).left)
    (x : (∏ᶜ C).left) :
    x ∈ puncturedProductOpen C Q ↔
      ∀ i, (Pi.π C i).left x ∉ closure ({Q i} : Set (C i).left) := sorry

end AlgebraicGeometry.SchemeOverField
