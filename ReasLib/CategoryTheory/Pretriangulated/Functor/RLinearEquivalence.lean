/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.Linear
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Linear Triangulated Equivalences

This leaf owns the data of an equivalence between `R`-linear pretriangulated
categories together with its shift, triangulated, and linear structures.  The
structures are retained for both quasi-inverse functors, so downstream users
can explicitly select the data carried by either direction.
-/

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe uR uDA uDB uDC vDA vDB vDC

namespace CategoryTheory

namespace RLinear

section

variable (R : Type uR) [CommRing R]
variable (DA : Type uDA) (DB : Type uDB)
variable [Category.{vDA} DA] [Category.{vDB} DB]
variable [HasZeroObject DA] [HasZeroObject DB]
variable [Preadditive DA] [Preadditive DB]
variable [Linear R DA] [Linear R DB]
variable [HasShift DA ℤ] [HasShift DB ℤ]
variable [∀ n : ℤ, (shiftFunctor DA n).Additive]
variable [∀ n : ℤ, (shiftFunctor DB n).Additive]
variable [Pretriangulated DA] [Pretriangulated DB]

/-- An `R`-linear equivalence of pretriangulated categories, including the
shift, triangulated, and linear structures for both quasi-inverse functors. -/
@[stacks 09SC "linear triangulated equivalence"]
structure TriangulatedEquivalence where
  /-- The underlying equivalence of categories. -/
  toEquivalence : DA ≌ DB
  /-- Shift compatibility of the forward functor. -/
  functor_commShift : toEquivalence.functor.CommShift ℤ
  /-- Shift compatibility of the inverse functor. -/
  inverse_commShift : toEquivalence.inverse.CommShift ℤ
  /-- Triangulatedness of the forward functor. -/
  functor_isTriangulated : toEquivalence.functor.IsTriangulated
  /-- Triangulatedness of the inverse functor. -/
  inverse_isTriangulated : toEquivalence.inverse.IsTriangulated
  /-- `R`-linearity of the forward functor. -/
  functor_linear : toEquivalence.functor.Linear R
  /-- `R`-linearity of the inverse functor. -/
  inverse_linear : toEquivalence.inverse.Linear R

end

namespace TriangulatedEquivalence

variable (R : Type uR) [CommRing R]
variable {DA : Type uDA} {DB : Type uDB}
variable [Category.{vDA} DA] [Category.{vDB} DB]
variable [HasZeroObject DA] [HasZeroObject DB]
variable [Preadditive DA] [Preadditive DB]
variable [Linear R DA] [Linear R DB]
variable [HasShift DA ℤ] [HasShift DB ℤ]
variable [∀ n : ℤ, (shiftFunctor DA n).Additive]
variable [∀ n : ℤ, (shiftFunctor DB n).Additive]
variable [Pretriangulated DA] [Pretriangulated DB]

/-- The forward functor underlying an `RLinear.TriangulatedEquivalence`. -/
abbrev functor (e : TriangulatedEquivalence R DA DB) : DA ⥤ DB :=
  e.toEquivalence.functor

/-- The inverse functor underlying an `RLinear.TriangulatedEquivalence`. -/
abbrev inverse (e : TriangulatedEquivalence R DA DB) : DB ⥤ DA :=
  e.toEquivalence.inverse

/-- Bundle an equivalence when the required structures on both quasi-inverse
functors are already available through typeclass search. -/
def ofEquivalence (e : DA ≌ DB)
    [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
    [e.functor.IsTriangulated] [e.inverse.IsTriangulated]
    [e.functor.Linear R] [e.inverse.Linear R] :
    TriangulatedEquivalence R DA DB where
  toEquivalence := e
  functor_commShift := inferInstance
  inverse_commShift := inferInstance
  functor_isTriangulated := inferInstance
  inverse_isTriangulated := inferInstance
  functor_linear := inferInstance
  inverse_linear := inferInstance

/- The adjunction-based constructor below is intentionally the canonical owner for equivalences
whose right adjoint is mathematically meaningful (for example, derived tensor--Hom pairs). -/

/-- Bundle an `R`-linear triangulated adjunction whose left functor is an equivalence.  The
resulting categorical equivalence keeps the specified right adjoint as its inverse, rather than
choosing an unrelated quasi-inverse via `Functor.asEquivalence`.  The right-adjoint shift,
triangulated, and linear structures are induced canonically from the adjunction. -/
@[stacks 09S7 "adjunction-based linear triangulated equivalence"]
noncomputable def ofAdjunction
    {F : DA ⥤ DB} {G : DB ⥤ DA} (adj : F ⊣ G) (hF : F.IsEquivalence)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R] :
    TriangulatedEquivalence R DA DB := by
  -- Local instance justification (proof-local temporary data): expose the supplied equivalence
  -- certificate only while `Adjunction.toEquivalence` packages the unit and counit.
  letI : F.IsEquivalence := hF
  exact
    { toEquivalence := adj.toEquivalence
      functor_commShift := by
        change F.CommShift ℤ
        infer_instance
      inverse_commShift := adj.rightAdjointCommShift ℤ
      functor_isTriangulated := by
        change F.IsTriangulated
        infer_instance
      inverse_isTriangulated := by
        -- Local instance justification (proof-local temporary data): the right-adjoint
        -- triangulation theorem consumes the adjunction-induced shift comparison.
        letI : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
        change G.IsTriangulated
        exact adj.isTriangulatedWith_rightAdjoint
      functor_linear := by
        change F.Linear R
        infer_instance
      inverse_linear := by
        change G.Linear R
        exact adj.right_adjoint_linear }

/- The projections below are kept as named rewrite points for downstream functor calculations. -/

/-- The forward functor of `ofAdjunction` is the specified left adjoint. -/
@[simp]
theorem ofAdjunction_functor
    {F : DA ⥤ DB} {G : DB ⥤ DA} (adj : F ⊣ G) (hF : F.IsEquivalence)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R] :
    (ofAdjunction R adj hF).functor = F := sorry

/- The inverse projection is equally important because it preserves the chosen right adjoint. -/

/-- The inverse functor of `ofAdjunction` is the specified right adjoint. -/
@[simp]
theorem ofAdjunction_inverse
    {F : DA ⥤ DB} {G : DB ⥤ DA} (adj : F ⊣ G) (hF : F.IsEquivalence)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R] :
    (ofAdjunction R adj hF).inverse = G := sorry

/-- Bundle an `R`-linear triangulated functor known to be an equivalence. The categorical
quasi-inverse is the canonical one selected by `Functor.asEquivalence`; its shift structure is
then induced from the forward shift structure. -/
noncomputable def ofFunctor (F : DA ⥤ DB) (hF : F.IsEquivalence)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R] :
    TriangulatedEquivalence R DA DB where
  toEquivalence := @Functor.asEquivalence DA _ DB _ F hF
  functor_commShift :=
    Functor.CommShift.ofIso
      (eqToIso (@Functor.asEquivalence_functor DA _ DB _ F hF)).symm ℤ
  inverse_commShift :=
    -- Local instance justification (instance diamond): the forward shift structure is
    -- transported only to construct mathlib's canonical inverse shift structure.
    letI : (@Functor.asEquivalence DA _ DB _ F hF).functor.CommShift ℤ :=
      Functor.CommShift.ofIso
        (eqToIso (@Functor.asEquivalence_functor DA _ DB _ F hF)).symm ℤ
    (@Functor.asEquivalence DA _ DB _ F hF).commShiftInverse ℤ
  functor_isTriangulated := sorry
  inverse_isTriangulated := sorry
  functor_linear := sorry
  inverse_linear := sorry

/-- The forward functor of `ofFunctor` is the original functor. -/
@[simp]
theorem ofFunctor_functor (F : DA ⥤ DB) (hF : F.IsEquivalence)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R] :
    (ofFunctor R F hF).functor = F := sorry

/-- Reverse a linear triangulated equivalence. -/
@[symm]
def symm (e : TriangulatedEquivalence R DA DB) :
    TriangulatedEquivalence R DB DA where
  toEquivalence := e.toEquivalence.symm
  functor_commShift := e.inverse_commShift
  inverse_commShift := e.functor_commShift
  functor_isTriangulated := e.inverse_isTriangulated
  inverse_isTriangulated := e.functor_isTriangulated
  functor_linear := e.inverse_linear
  inverse_linear := e.functor_linear

/-- The identity linear triangulated equivalence. -/
@[refl]
def refl : TriangulatedEquivalence R DA DA where
  toEquivalence := Equivalence.refl
  functor_commShift := inferInstance
  inverse_commShift := inferInstance
  functor_isTriangulated := sorry
  inverse_isTriangulated := sorry
  functor_linear := sorry
  inverse_linear := sorry

variable {DC : Type uDC} [Category.{vDC} DC]
variable [HasZeroObject DC] [Preadditive DC] [Linear R DC]
variable [HasShift DC ℤ] [∀ n : ℤ, (shiftFunctor DC n).Additive]
variable [Pretriangulated DC]

/-- Compose linear triangulated equivalences. -/
@[trans]
def trans (e : TriangulatedEquivalence R DA DB)
    (e' : TriangulatedEquivalence R DB DC) :
    TriangulatedEquivalence R DA DC where
  toEquivalence := e.toEquivalence.trans e'.toEquivalence
  functor_commShift :=
    @Functor.CommShift.comp _ _ _ _ _ _ e.functor e'.functor ℤ _ _ _ _
      e.functor_commShift e'.functor_commShift
  inverse_commShift :=
    @Functor.CommShift.comp _ _ _ _ _ _ e'.inverse e.inverse ℤ _ _ _ _
      e'.inverse_commShift e.inverse_commShift
  functor_isTriangulated := sorry
  inverse_isTriangulated := sorry
  functor_linear := sorry
  inverse_linear := sorry

/-- Reversing an equivalence exchanges its forward and inverse functors. -/
@[simp]
theorem symm_functor (e : TriangulatedEquivalence R DA DB) :
    (symm R e).functor = e.inverse := sorry

/-- The inverse functor of the reversed equivalence is the original forward functor. -/
@[simp]
theorem symm_inverse (e : TriangulatedEquivalence R DA DB) :
    (symm R e).inverse = e.functor := sorry

/-- The forward functor of the identity equivalence is the identity functor. -/
@[simp]
theorem refl_functor : (refl R (DA := DA)).functor = 𝟭 DA := sorry

/-- The forward functor of a composite equivalence is the composite of the forward functors. -/
@[simp]
theorem trans_functor (e : TriangulatedEquivalence R DA DB)
    (e' : TriangulatedEquivalence R DB DC) :
    (trans R e e').functor = e.functor ⋙ e'.functor := sorry

/-- The inverse functor of a composite equivalence is the reverse composite of the inverses. -/
@[simp]
theorem trans_inverse (e : TriangulatedEquivalence R DA DB)
    (e' : TriangulatedEquivalence R DB DC) :
    (trans R e e').inverse = e'.inverse ⋙ e.inverse := sorry

end TriangulatedEquivalence

end RLinear

end CategoryTheory
