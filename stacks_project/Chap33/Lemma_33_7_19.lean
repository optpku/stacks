/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.ConnectedComponents.Finite
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.ConnectedComponents.Continuity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Compact

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

/- Lemma 33.7.19 (1) (Tag 038E): finiteness of connected components after a compact-open
separable-closure base change. -/
@[stacks 038E] #check
  (AlgebraicGeometry.FieldExtension.Connected.finite_components_of_compact_open :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [CompactSpace X],
      (∀ x : FieldExtension.baseChange k K f, IsOpen (connectedComponent x)) →
        Finite (ConnectedComponents (FieldExtension.baseChange k K f)))

/- Lemma 33.7.19 (2) (Tag 038E): continuity of the induced Galois action. -/
@[stacks 038E] #check
  (AlgebraicGeometry.FieldExtension.Galois.Connected.Continuity.continuousSMul_of_compact_open :
    ∀ {k ksep : Type u} [Field k] [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [CompactSpace X],
      (∀ x : FieldExtension.baseChange k ksep f, IsOpen (connectedComponent x)) →
        ContinuousSMul Gal(ksep/k)
          (ConnectedComponents (FieldExtension.baseChange k ksep f)))

/- Lemma 33.7.19 (3) (Tag 038E): finite type over a field supplies compactness of the source. -/
@[stacks 038E] #check
  (AlgebraicGeometry.Scheme.Hom.compactSpace_of_finiteType_over_field :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [Scheme.Hom.FiniteType f], CompactSpace X)

/- Lemma 33.7.19 (4) (Tag 038E): connected components of a finite-type geometric base change are
open. -/
@[stacks 038E] #check
  (AlgebraicGeometry.FieldExtension.Connected.isOpen_component_of_finiteType :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Scheme.Hom.FiniteType f]
      (x : FieldExtension.baseChange k K f), IsOpen (connectedComponent x))
