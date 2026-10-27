/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TorDimension.Descent
import StacksCheckRecall

/-! # Fpqc descent of relative Tor-amplitude on algebraic spaces -/

open AlgebraicGeometry AlgebraicSpace CategoryTheory

universe u v

open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/- Lemma 76.54.2 (1). Relative Tor-amplitude in a fixed interval descends along an fpqc covering
of the base for complexes with quasi-coherent cohomology. -/
@[stacks 0DL2]
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.hasTorAmplitudeInOver_iff_fpqcCovering :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {ι : Type v}
    (f : X ⟶ Y) (family : ι → Over Y) (hfamily : FpqcCovering family)
    (E : ModuleDerived X) (hE : derivedQuasiCoherentModuleProperty X E)
    (a b : ℤ),
    HasTorAmplitudeInOver f E a b ↔
      ∀ i, HasTorAmplitudeInOver (overPullbackFst f (family i))
        ((modulePullbackDerived (overPullbackSnd f (family i))).obj E) a b)

/- Lemma 76.54.2 (2). Locally finite relative Tor dimension descends along the same fpqc covering. -/
@[stacks 0DL2]
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.locallyFiniteTorDimensionOver_iff_fpqcCovering :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {ι : Type v}
    (f : X ⟶ Y) (family : ι → Over Y) (hfamily : FpqcCovering family)
    (E : ModuleDerived X) (hE : derivedQuasiCoherentModuleProperty X E),
    locallyFiniteTorDimensionOver f E ↔
      ∀ i, locallyFiniteTorDimensionOver (overPullbackFst f (family i))
        ((modulePullbackDerived (overPullbackSnd f (family i))).obj E))
