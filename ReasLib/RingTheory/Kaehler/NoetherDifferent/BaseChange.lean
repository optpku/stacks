/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.RingTheory.Algebra.TensorProduct.BaseChange
public import ReasLib.RingTheory.Kaehler.NoetherDifferent

@[expose] public section

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace KaehlerDifferential

/-- Under a flat extension of scalars, the annihilator of the diagonal ideal is
the extension of the original annihilator. -/
theorem annihilator_baseChange (A : Type u) (A' : Type v) (B : Type w)
    [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A B]
    [Algebra.FiniteType A B] [Module.Flat A A'] :
    (ideal A' (A' ⊗[A] B)).annihilator =
      Ideal.map (diagonalBaseChange A A' B) (ideal A B).annihilator := sorry

/-- The Noether different commutes with flat extension of scalars for algebras
of finite type. -/
theorem noetherDifferent_baseChange (A : Type u) (A' : Type v) (B : Type w)
    [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A B]
    [Algebra.FiniteType A B] [Module.Flat A A'] :
    noetherDifferent A' (A' ⊗[A] B) =
      Ideal.map includeRight (noetherDifferent A B) := sorry

/-- A cartesian base change carries an element annihilating the diagonal ideal
to an element annihilating the base-changed diagonal ideal. -/
theorem diagonalMap_mem_annihilator
    (A A₁ : Type u) (B B₁ : Type v)
    [CommRing A] [CommRing A₁] [CommRing B] [CommRing B₁]
    [Algebra A A₁] [Algebra A B] [Algebra A₁ B₁] [Algebra A B₁]
    [IsScalarTower A A₁ B₁] [Algebra B B₁] [IsScalarTower A B B₁]
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B B₁).toLinearMap)
    (xi : (ideal A B).annihilator) :
    Algebra.TensorProduct.diagonalMap A A₁ B B₁ xi.1 ∈
      (ideal A₁ B₁).annihilator := sorry

end KaehlerDifferential
