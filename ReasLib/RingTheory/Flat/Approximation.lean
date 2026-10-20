/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

universe u

namespace Algebra.FlatApproximation

/-- There exists a flat commutative algebra that is not a filtered colimit of finitely
presented flat algebras over its base ring. -/
theorem exists_counterexample :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B),
      Module.Flat A B ∧ ¬ CategoryTheory.ObjectProperty.ind.{u}
        (fun C : CommAlgCat.{u} A => Algebra.FinitePresentation A C ∧ Module.Flat A C)
        (CommAlgCat.of A B) := sorry

/-- There exists a finite type algebra over a prime field admitting a flat commutative
algebra that is not a filtered colimit of finitely presented flat algebras. -/
theorem exists_finiteType_counterexample :
    ∃ (p : ℕ) (_ : Fact p.Prime) (A B : Type u)
      (_ : CommRing A) (_ : CommRing B) (_ : Algebra (ZMod p) A) (_ : Algebra A B),
      Algebra.FiniteType (ZMod p) A ∧
        Module.Flat A B ∧ ¬ CategoryTheory.ObjectProperty.ind.{u}
          (fun C : CommAlgCat.{u} A => Algebra.FinitePresentation A C ∧ Module.Flat A C)
          (CommAlgCat.of A B) := sorry

/-- There exists a one-dimensional Noetherian local ring with residue field of
characteristic zero admitting a flat commutative algebra that is not a filtered colimit
of finitely presented flat algebras. -/
theorem exists_noetherianLocal_counterexample :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B)
      (_ : IsLocalRing A) (_ : IsNoetherianRing A),
      ringKrullDim A = 1 ∧ CharZero (IsLocalRing.ResidueField A) ∧
        Module.Flat A B ∧ ¬ CategoryTheory.ObjectProperty.ind.{u}
          (fun C : CommAlgCat.{u} A => Algebra.FinitePresentation A C ∧ Module.Flat A C)
          (CommAlgCat.of A B) := sorry

end Algebra.FlatApproximation
