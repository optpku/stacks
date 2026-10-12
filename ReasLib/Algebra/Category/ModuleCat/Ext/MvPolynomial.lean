/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.RingTheory.Sequence.Koszul.MvPolynomial

@[expose] public section

noncomputable section

universe u

open CategoryTheory MvPolynomial

namespace MvPolynomial

/-- The quotient module `R ⧸ (x, y)` has finite Ext groups over its coefficient field. -/
instance finite_ext_quotient_span_XY (k : Type u) [Field k] (i : ℕ) :
    Module.Finite k
      (Abelian.Ext
        (ModuleCat.of (MvPolynomial (Fin 2) k) (quotientSpanXY k))
        (ModuleCat.of (MvPolynomial (Fin 2) k) (quotientSpanXY k)) i) :=
  sorry

/-- The `k`-dimension of the self-Ext groups of `R ⧸ (x, y)` is `Nat.choose 2 i`. -/
theorem ext_finrank_quotient_span_XY (k : Type u) [Field k] (i : ℕ) :
    Module.finrank k
      (Abelian.Ext
        (ModuleCat.of (MvPolynomial (Fin 2) k) (quotientSpanXY k))
        (ModuleCat.of (MvPolynomial (Fin 2) k) (quotientSpanXY k)) i) =
      Nat.choose 2 i :=
  sorry

end MvPolynomial
