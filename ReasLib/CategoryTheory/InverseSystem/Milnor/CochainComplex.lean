module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Milnor

/-!
# Milnor Cochain Complexes of Sequential Inverse Systems

This leaf realizes the product-level Milnor difference map of a sequential inverse system as the
explicit two-term cochain complex concentrated in degrees `0` and `1`.  It is independent of any
derived-category construction.
@stack 07KW
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

noncomputable section

universe u v

namespace CategoryTheory.SequentialInverseSystem

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
  [HasCountableProducts C]

/-- The term in degree `n` of the two-term Milnor cochain complex of `K`: the product of the
stages in degrees `0` and `1`, and zero elsewhere. -/
noncomputable def milnorCochainTerm (K : SequentialInverseSystem C) (n : ℤ) : C :=
  if n = 0 ∨ n = 1 then ∏ᶜ K.family else 0

/-- The differential of the two-term Milnor cochain complex: it is the canonical difference map
in degree `0` and zero in every other degree. -/
noncomputable def milnorCochainDifferential
    (K : SequentialInverseSystem C) (n : ℤ) :
    milnorCochainTerm K n ⟶ milnorCochainTerm K (n + 1) :=
  if hn : n = 0 then
    eqToHom (by subst n; simp [milnorCochainTerm]) ≫
      K.milnorDifferenceMap ≫
        eqToHom (by subst n; simp [milnorCochainTerm])
  else 0

/-- The Milnor cochain differential squares to zero. -/
theorem milnorCochainDifferential_sq_zero
    (K : SequentialInverseSystem C) (n : ℤ) :
    milnorCochainDifferential K n ≫ milnorCochainDifferential K (n + 1) = 0 := sorry

/-- Lemma 15.87.1 [07KW]: the explicit cochain complex with the Milnor difference map from
degree `0` to degree `1`. -/
@[stacks 07KW]
noncomputable def milnorCochainComplex (K : SequentialInverseSystem C) : CochainComplex C ℤ :=
  CochainComplex.of
    (milnorCochainTerm K)
    (milnorCochainDifferential K)
    (milnorCochainDifferential_sq_zero K)

/-- The terms of `milnorCochainComplex` are the advertised two-term Milnor term function. -/
@[simp]
theorem milnorCochainComplex_X
    (K : SequentialInverseSystem C) (n : ℤ) :
    (milnorCochainComplex K).X n = milnorCochainTerm K n := sorry

/-- The only nonzero differential of `milnorCochainComplex` is its degree-`0` Milnor difference
map. -/
@[simp]
theorem milnorCochainComplex_d_zero
    (K : SequentialInverseSystem C) :
    (milnorCochainComplex K).d 0 1 = K.milnorDifferenceMap := sorry

end CategoryTheory.SequentialInverseSystem
