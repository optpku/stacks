/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.Approximation
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 110.76.1 (1): there exists a commutative ring `A` and a flat `A`-algebra `B` which cannot
be written as a filtered colimit of finitely presented flat `A`-algebras. -/
@[stacks 0ATF] #check (Algebra.FlatApproximation.exists_counterexample.{u} :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B),
      Module.Flat A B ∧ ¬ CategoryTheory.ObjectProperty.ind.{u}
        (fun C : CommAlgCat.{u} A => Algebra.FinitePresentation A C ∧ Module.Flat A C)
        (CommAlgCat.of A B))

/- Lemma 110.76.1 (2): there exists a finite type `ZMod p`-algebra `A` and a flat `A`-algebra `B`
which cannot be written as a filtered colimit of finitely presented flat `A`-algebras. -/
@[stacks 0ATF] #check (Algebra.FlatApproximation.exists_finiteType_counterexample.{u} :
    ∃ (p : ℕ) (_ : Fact p.Prime) (A B : Type u)
      (_ : CommRing A) (_ : CommRing B) (_ : Algebra (ZMod p) A) (_ : Algebra A B),
      Algebra.FiniteType (ZMod p) A ∧
        Module.Flat A B ∧ ¬ CategoryTheory.ObjectProperty.ind.{u}
          (fun C : CommAlgCat.{u} A => Algebra.FinitePresentation A C ∧ Module.Flat A C)
          (CommAlgCat.of A B))

/- Lemma 110.76.1 (3): there exists a 1-dimensional Noetherian local ring `A` whose residue field
has characteristic 0, and a flat `A`-algebra `B` which cannot be written as a filtered colimit of
finitely presented flat `A`-algebras. -/
@[stacks 0ATF] #check (Algebra.FlatApproximation.exists_noetherianLocal_counterexample.{u} :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B)
      (_ : IsLocalRing A) (_ : IsNoetherianRing A),
      ringKrullDim A = 1 ∧ CharZero (IsLocalRing.ResidueField A) ∧
        Module.Flat A B ∧ ¬ CategoryTheory.ObjectProperty.ind.{u}
          (fun C : CommAlgCat.{u} A => Algebra.FinitePresentation A C ∧ Module.Flat A C)
          (CommAlgCat.of A B))
