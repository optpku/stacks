/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.SchemeComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative

/-! # Relative pseudo-coherence on represented algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

namespace IsMPseudoCoherentOver

/-- A quasi-coherent derived module on a represented algebraic space is relatively
`m`-pseudo-coherent when every scheme-derived comparison preimage is relatively
`m`-pseudo-coherent over the representing target scheme. -/
def ofOver {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    [LocallyOfFiniteType (ofOverMap f0)]
    (E : ModuleDerived (AlgebraicSpace.ofOver X0))
    (hE : derivedQuasiCoherentModuleProperty (AlgebraicSpace.ofOver X0) E)
    (m : ℤ) : Prop :=
  ∀ E0 : Scheme.DerivedQCoh X0.left,
    isEpsilonStarPullback X0 E E0 →
      AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver f0.left E0.obj m

/-- Relative `m`-pseudo-coherence on a represented algebraic space is equivalent to
relative `m`-pseudo-coherence of some scheme-derived comparison preimage. -/
theorem ofOver_iff {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    [LocallyOfFiniteType (ofOverMap f0)]
    (E : ModuleDerived (AlgebraicSpace.ofOver X0))
    (hE : derivedQuasiCoherentModuleProperty (AlgebraicSpace.ofOver X0) E)
    (m : ℤ) :
    ofOver f0 E hE m ↔
      ∃ E0 : Scheme.DerivedQCoh X0.left,
        isEpsilonStarPullback X0 E E0 ∧
          AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver f0.left E0.obj m :=
  sorry

/-- Relative `m`-pseudo-coherence on a represented algebraic space implies relative
`m`-pseudo-coherence of every scheme-derived comparison preimage. -/
theorem ofOver_spec {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    [LocallyOfFiniteType (ofOverMap f0)]
    {E : ModuleDerived (AlgebraicSpace.ofOver X0)}
    {hE : derivedQuasiCoherentModuleProperty (AlgebraicSpace.ofOver X0) E}
    {m : ℤ} (h : ofOver f0 E hE m) {E0 : Scheme.DerivedQCoh X0.left}
    (hE0 : isEpsilonStarPullback X0 E E0) :
    AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver f0.left E0.obj m :=
  h E0 hE0

end IsMPseudoCoherentOver

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
