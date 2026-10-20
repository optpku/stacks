/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.ConnectedComponents.Descent
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Comparison

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

section Action

variable (k ksep : Type u) [Field k] [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
variable {X : AlgebraicGeometry.Scheme.{u}}
  (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))

/- Lemma 33.7.18 (action): the opposite Galois group acts canonically on the connected
components of the separable-closure base change. -/
@[stacks 038D] #check
  (AlgebraicGeometry.FieldExtension.Galois.Connected.instOppositeMulAction k ksep f :
    MulAction (Gal(ksep / k))ᵐᵒᵖ
      (ConnectedComponents (AlgebraicGeometry.FieldExtension.baseChange k ksep f)))

end Action

/- Lemma 33.7.18 (1): a connected component of a separable-closure base change is fixed by the
opposite Galois action exactly when it descends from a geometrically connected component. -/
@[stacks 038D] #check
  (AlgebraicGeometry.FieldExtension.Galois.Connected.Descent.op_fixed_iff_exists :
    ∀ {k ksep : Type u} [Field k] [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      (Tbar : ConnectedComponents (AlgebraicGeometry.FieldExtension.baseChange k ksep f)),
      (∀ σ : (Gal(ksep / k))ᵐᵒᵖ, σ • Tbar = Tbar) ↔
        ∃ C : ConnectedComponents X,
          AlgebraicGeometry.GeometricallyConnected.Components.isConnected f C ∧
            (AlgebraicGeometry.FieldExtension.toSource k ksep f).base ⁻¹' C.set = Tbar.set)

/- Lemma 33.7.18 (2a): the comparison map on connected components attached to an explicit
embedding of separable closures is bijective. -/
@[stacks 038D] #check
  (AlgebraicGeometry.FieldExtension.Galois.SepClosure.map_bijective :
    ∀ (k k' ksep ksep' : Type u)
      [Field k] [Field k'] [Field ksep] [Field ksep']
      [Algebra k k'] [Algebra k ksep] [Algebra k' ksep'] [IsSepClosure k ksep]
      [IsSepClosure k' ksep'] [Algebra k ksep'] [IsScalarTower k k' ksep']
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (i : ksep →ₐ[k] ksep'),
      Function.Bijective
        (AlgebraicGeometry.FieldExtension.Comparison.connectedComponentsMap f i))

/- Lemma 33.7.18 (2b): the comparison map intertwines the Galois actions through restriction
along the chosen embedding of separable closures. -/
@[stacks 038D] #check
  (AlgebraicGeometry.FieldExtension.Galois.SepClosure.map_commutes_galois :
    ∀ (k k' ksep ksep' : Type u)
      [Field k] [Field k'] [Field ksep] [Field ksep']
      [Algebra k k'] [Algebra k ksep] [Algebra k' ksep'] [IsSepClosure k ksep]
      [IsSepClosure k' ksep'] [Algebra k ksep'] [IsScalarTower k k' ksep']
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (i : ksep →ₐ[k] ksep')
      (σ : Gal(ksep' / k'))
      (C : ConnectedComponents (AlgebraicGeometry.FieldExtension.baseChange k ksep' f)),
      AlgebraicGeometry.FieldExtension.Comparison.connectedComponentsMap f i
          (Continuous.connectedComponentsMap
            ((AlgebraicGeometry.FieldExtension.Galois.SepClosure.pullback
              k k' ksep' f σ).continuous) C) =
        AlgebraicGeometry.FieldExtension.Galois.SepClosure.restrict
            k k' ksep ksep' i σ •
          AlgebraicGeometry.FieldExtension.Comparison.connectedComponentsMap f i C)
