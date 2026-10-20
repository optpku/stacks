/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.IrreducibleComponents.FixedPoints

@[expose] public section

open CategoryTheory

universe u

/- The opposite-Galois action on irreducible components is induced by the corresponding
base-change automorphism. -/
#check
  (AlgebraicGeometry.FieldExtension.Galois.Irreducible.op_smul_def :
    ∀ (k ksep : Type u) [Field k] [Field ksep] [Algebra k ksep]
      {X : AlgebraicGeometry.Scheme.{u}},
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) →
      (σ : (Gal(ksep/k))ᵐᵒᵖ) →
      (Tbar : irreducibleComponents
        (AlgebraicGeometry.FieldExtension.baseChange k ksep f)) →
      σ • Tbar =
        AlgebraicGeometry.FieldExtension.Galois.Irreducible.opEquiv
          k ksep f σ Tbar)

/- Lemma 33.8.13: the fixed irreducible components after base change to a separable closure are
exactly the pullbacks of geometrically irreducible components over the base field. -/
@[stacks 038J] #check
  (AlgebraicGeometry.FieldExtension.Galois.Irreducible.mem_fixedPoints_iff_exists_geometricallyIrreducibleComponent :
    ∀ (k ksep : Type u) [Field k] [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
      {X : AlgebraicGeometry.Scheme.{u}},
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) →
      (Tbar : irreducibleComponents
        (AlgebraicGeometry.FieldExtension.baseChange k ksep f)) →
      Tbar ∈ MulAction.fixedPoints (Gal(ksep/k))ᵐᵒᵖ
          (irreducibleComponents
            (AlgebraicGeometry.FieldExtension.baseChange k ksep f)) ↔
        ∃ T : irreducibleComponents X,
          AlgebraicGeometry.GeometricallyIrreducible
              (X.irreducibleComponentSubschemeι T ≫ f) ∧
            AlgebraicGeometry.FieldExtension.Galois.Closeds.preimage k ksep f
                (X.irreducibleComponentClosed T) =
              (AlgebraicGeometry.FieldExtension.baseChange k ksep f).irreducibleComponentClosed
                Tbar)

/- The comparison equivalence associated to a compatible embedding of separable closures
intertwines the opposite-Galois actions through restriction. -/
#check
  (AlgebraicGeometry.FieldExtension.Galois.SepClosure.equiv_commutes_galois :
    ∀ (k k' ksep ksep' : Type u)
      [Field k] [Field k'] [Field ksep] [Field ksep']
      [Algebra k k'] [Algebra k ksep] [Algebra k' ksep'] [IsSepClosure k ksep]
      [IsSepClosure k' ksep'] [Algebra k ksep'] [IsScalarTower k k' ksep']
      {X : AlgebraicGeometry.Scheme.{u}},
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) →
      (i : ksep →ₐ[k] ksep') →
      (σ : Gal(ksep'/k')) →
      (Tbar : irreducibleComponents
        (AlgebraicGeometry.FieldExtension.baseChange k' ksep'
          (AlgebraicGeometry.FieldExtension.toBase k k' f))) →
      AlgebraicGeometry.FieldExtension.Galois.SepClosure.componentsEquiv
          k k' ksep ksep' f i (MulOpposite.op σ • Tbar) =
        MulOpposite.op
            (AlgebraicGeometry.FieldExtension.Galois.SepClosure.restrict
              k k' ksep ksep' i σ) •
          AlgebraicGeometry.FieldExtension.Galois.SepClosure.componentsEquiv
            k k' ksep ksep' f i Tbar)
