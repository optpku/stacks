/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Topology
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

/- Lemma 29.21.10: if `X` is of finite presentation over a quasi-compact and quasi-separated
base `S`, then `X` is quasi-compact and quasi-separated. -/
@[stacks 01TY] #check
  (AlgebraicGeometry.Scheme.Hom.compactSpace_and_quasiSeparatedSpace_of_finitePresentation :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [CompactSpace S]
      [QuasiSeparatedSpace S] [AlgebraicGeometry.Scheme.Hom.FinitePresentation f],
      CompactSpace X ∧ QuasiSeparatedSpace X)

#check
  (AlgebraicGeometry.Scheme.Hom.compactSpace_of_finitePresentation :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [CompactSpace S]
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation f], CompactSpace X)

#check
  (AlgebraicGeometry.Scheme.Hom.quasiSeparatedSpace_of_finitePresentation :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [QuasiSeparatedSpace S]
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation f], QuasiSeparatedSpace X)
