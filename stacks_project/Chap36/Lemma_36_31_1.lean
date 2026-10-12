/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberBetti

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 36.31.1 (1): formation of the degreewise fiber Betti function of a
pseudo-coherent derived module commutes with arbitrary scheme base change. -/
@[stacks 0BDI] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti_pullback :
    {X Y : Scheme.{u}} → (f : Y ⟶ X) →
      (E : RingedSpace.ModuleDerived X.toRingedSpace) →
      RingedSpace.ModuleDerived.IsPseudoCoherent E → (i : ℤ) →
      AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti
          ((RingedSpace.modulePullbackDerived f.toShHom).obj E) i =
        fun y : Y ↦ AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti E i (f y))

/- Lemma 36.31.1 (2): every degreewise fiber Betti function of a pseudo-coherent
derived module is upper semicontinuous. -/
@[stacks 0BDI] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti_upperSemicontinuous :
    {X : Scheme.{u}} → (E : RingedSpace.ModuleDerived X.toRingedSpace) →
      RingedSpace.ModuleDerived.IsPseudoCoherent E → (i : ℤ) →
      UpperSemicontinuous (AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti E i))

/- Lemma 36.31.1 (3): every level set of a degreewise fiber Betti function of a
pseudo-coherent derived module is locally constructible. -/
@[stacks 0BDI] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti_levelSet_isLocallyConstructible :
    {X : Scheme.{u}} → (E : RingedSpace.ModuleDerived X.toRingedSpace) →
      RingedSpace.ModuleDerived.IsPseudoCoherent E → (i : ℤ) → (n : ℕ) →
      Topology.IsLocallyConstructible
        ((AlgebraicGeometry.Scheme.ModuleDerived.fiberBetti E i) ⁻¹' {n}))
