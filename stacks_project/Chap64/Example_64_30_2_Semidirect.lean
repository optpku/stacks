/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.AddAut
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.GroupTheory.GroupExtension.Defs
public import stacks_project.Chap64.Example_64_30_2_PrimeTo

/-!
# Semidirect product of `PadicInt.PrimeTo q` by `Multiplicative ℤ`

The conjugation extension `1 → PadicInt.PrimeTo q → Γ → Multiplicative ℤ → 1`
with `F ↦ 1` and `F x F⁻¹ = u x` for a unit `u`.
-/

@[expose] public section

noncomputable section

namespace PadicInt.PrimeTo

/-- The action of `Multiplicative ℤ` on `Multiplicative (PadicInt.PrimeTo q)` by
powers of left multiplication by `u`. -/
def intMulAut (q : ℕ) (u : (PrimeTo q)ˣ) :
    Multiplicative ℤ →* MulAut (Multiplicative (PrimeTo q)) :=
  (MulEquiv.toMonoidHom (MulAutMultiplicative (PrimeTo q)).symm).comp
    (AddAut.mulLeft.comp (zpowersHom (PrimeTo q)ˣ u))

/-- The semidirect product `Multiplicative (PadicInt.PrimeTo q) ⋊ Multiplicative ℤ`
implementing the extension with conjugation by the unit `u`. -/
abbrev semidirect (q : ℕ) (u : (PrimeTo q)ˣ) :=
  Multiplicative (PrimeTo q) ⋊[intMulAut q u] Multiplicative ℤ

/-- The degree-one element `F` in `PadicInt.PrimeTo.semidirect q u`, mapping to `1`
in `Multiplicative ℤ`. -/
def frobenius (q : ℕ) (u : (PrimeTo q)ˣ) : semidirect q u :=
  ⟨1, Multiplicative.ofAdd 1⟩

/-- The group extension `1 → Multiplicative (PadicInt.PrimeTo q) →
PadicInt.PrimeTo.semidirect q u → Multiplicative ℤ → 1`. -/
def groupExtension (q : ℕ) (u : (PrimeTo q)ˣ) :
    GroupExtension (Multiplicative (PrimeTo q)) (semidirect q u) (Multiplicative ℤ) :=
  SemidirectProduct.toGroupExtension (intMulAut q u)

/-- The image of `PadicInt.PrimeTo.frobenius` under the quotient map is the generator
`Multiplicative.ofAdd 1`. -/
theorem rightHom_frobenius (q : ℕ) (u : (PrimeTo q)ˣ) :
    (groupExtension q u).rightHom (frobenius q u) = Multiplicative.ofAdd 1 := sorry

/-- Conjugation by `PadicInt.PrimeTo.frobenius` is left multiplication by `u` on
`PadicInt.PrimeTo q`. -/
theorem conjAct_frobenius (q : ℕ) (u : (PrimeTo q)ˣ)
    (x : Multiplicative (PrimeTo q)) :
    (groupExtension q u).conjAct (frobenius q u) x =
      Multiplicative.ofAdd (u.val * x.toAdd) := sorry

end PadicInt.PrimeTo

