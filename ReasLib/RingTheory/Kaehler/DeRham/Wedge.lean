/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Map
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Wedge multiplication on relative differential forms

This file constructs the canonical wedge product on the quotient presentation of relative
differential forms and packages it for morphisms of commutative rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace KaehlerDifferential.DeRham

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Concatenation and multiplication on two formal linear combinations of basic forms. -/
def freeWedgeFun (p q : ℕ) (x : Free B p) (y : Free B q) : Form A B (p + q) :=
  x.sum fun x r ↦ y.sum fun y s ↦
    (r * s) • basic A B (p + q) (x.1 * y.1) (Fin.append x.2 y.2)

/-- Formal wedge multiplication is additive in its left argument. -/
theorem freeWedgeFun_add_left (p q : ℕ) (x x' : Free B p) (y : Free B q) :
    freeWedgeFun A B p q (x + x') y =
      freeWedgeFun A B p q x y + freeWedgeFun A B p q x' y := sorry

/-- Formal wedge multiplication is linear in its left argument. -/
theorem freeWedgeFun_smul_left (p q : ℕ) (r : B) (x : Free B p) (y : Free B q) :
    freeWedgeFun A B p q (r • x) y = r • freeWedgeFun A B p q x y := sorry

/-- Formal wedge multiplication is additive in its right argument. -/
theorem freeWedgeFun_add_right (p q : ℕ) (x : Free B p) (y y' : Free B q) :
    freeWedgeFun A B p q x (y + y') =
      freeWedgeFun A B p q x y + freeWedgeFun A B p q x y' := sorry

/-- Formal wedge multiplication is linear in its right argument. -/
theorem freeWedgeFun_smul_right (p q : ℕ) (r : B) (x : Free B p) (y : Free B q) :
    freeWedgeFun A B p q x (r • y) = r • freeWedgeFun A B p q x y := sorry

/-- The bilinear formal wedge map before passing to the form quotients. -/
def freeWedge (p q : ℕ) :
    Free B p →ₗ[B] Free B q →ₗ[B] Form A B (p + q) :=
  LinearMap.mk₂ B (freeWedgeFun A B p q)
    (freeWedgeFun_add_left A B p q) (freeWedgeFun_smul_left A B p q)
    (freeWedgeFun_add_right A B p q) (freeWedgeFun_smul_right A B p q)

/-- Relations among degree-`p` forms vanish under formal wedge multiplication. -/
theorem relations_le_ker_freeWedge (p q : ℕ) :
    relations A B p ≤ LinearMap.ker (freeWedge A B p q) := sorry

/-- Relations among degree-`q` forms vanish in the right argument of formal wedge multiplication. -/
theorem relations_le_ker_freeWedge_flip (p q : ℕ) :
    relations A B q ≤ LinearMap.ker (freeWedge A B p q).flip := sorry

/-- The canonical bilinear wedge product on the quotient presentation of relative forms. -/
def formWedgeBilinear (p q : ℕ) :
    Form A B p →ₗ[B] Form A B q →ₗ[B] Form A B (p + q) :=
  (freeWedge A B p q).liftQ₂ (relations A B p) (relations A B q)
    (relations_le_ker_freeWedge A B p q)
    (relations_le_ker_freeWedge_flip A B p q)

/-- The canonical multiplication `Ω^p_{B/A} ⊗ Ω^q_{B/A} ⟶ Ω^(p+q)_{B/A}`. -/
def formWedge (p q : ℕ) :
    form A B p ⊗ form A B q ⟶ form A B (p + q) :=
  ModuleCat.ofHom (TensorProduct.lift (formWedgeBilinear A B p q))

/-- Wedge multiplication concatenates two basic relative forms. -/
theorem formWedge_basic (p q : ℕ) (b₀ c₀ : B)
    (bs : Fin p → B) (cs : Fin q → B) :
    formWedge A B p q (basic A B p b₀ bs ⊗ₜ basic A B q c₀ cs) =
      basic A B (p + q) (b₀ * c₀) (Fin.append bs cs) := sorry

end KaehlerDifferential.DeRham

namespace CommRingCat.DeRham

variable {A B : CommRingCat.{u}}

/-- The canonical wedge product on relative forms associated to a morphism of rings. -/
noncomputable def formWedge (f : A ⟶ B) (p q : ℕ) :
    form f p ⊗ form f q ⟶ form f (p + q) :=
  -- Local instance justification (defeq pin): match the algebra structure used by `form f`.
  letI := f.hom.toAlgebra
  KaehlerDifferential.DeRham.formWedge A B p q

/-- The categorical wedge product concatenates two basic relative forms. -/
theorem formWedge_basic (f : A ⟶ B) (p q : ℕ) (b₀ c₀ : B)
    (bs : Fin p → B) (cs : Fin q → B) :
    formWedge f p q (basic f p b₀ bs ⊗ₜ basic f q c₀ cs) =
      basic f (p + q) (b₀ * c₀) (Fin.append bs cs) := sorry

end CommRingCat.DeRham
