/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.WeakIdealCompletion.FiniteType
import StacksCheckRecall

/-!
# Example 87.24.7

If `A` is weakly admissible over a scheme `S` and `A → A'` is a finite-type
ring map, then the weak-ideal completion `(A')^∧` is weakly admissible and
`Spf((A')^∧) ⟶ Spf(A)` is representable, as in Example 87.19.11. A map from a
quasi-compact scheme into `Spf(A)` factors through some `Spec(A ⧸ I)` by
Lemma 87.9.4, the fibre product with `Spf((A')^∧)` is identified with the
affine comparison `Spec(A' ⧸ I A') ⟶ Spec(A ⧸ I)`, and therefore
`Spf((A')^∧) ⟶ Spf(A)` is of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Example 87.24.7 (1): The quotient-stage comparison is the base change of
`Spf((A')^∧) ⟶ Spf(A)` along the canonical map `Spec(A ⧸ I) ⟶ Spf(A)`. -/
@[stacks 0ANM] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.isPullback_quotientStage :
    ∀ {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
      [IsWeaklyAdmissibleRing A] (hA : Spec (.of A) ⟶ S)
      [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
      (A' : Type u) [CommRing A'] [Algebra A A'] (I : WeakIdealOfDefinition A),
      IsPullback
        ((presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (yoneda.map (quotientStageMap hA A' I)))
        (quotientStageι hA A' I) (spfι A hA I) (spfMap_weakIdealCompletion hA A'))

/- Example 87.24.7 (2): The weak-ideal completion of a finite-type algebra
induces a finite-type morphism of formal spectra. -/
@[stacks 0ANM] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.instFiniteType_spfMap_weakIdealCompletion :
    ∀ {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
      [IsWeaklyAdmissibleRing A] (hA : Spec (.of A) ⟶ S)
      [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
      (A' : Type u) [CommRing A'] [Algebra A A'] [Algebra.FiniteType A A'],
      FormalAlgebraicSpace.FiniteType (spfMap_weakIdealCompletion hA A').hom)
