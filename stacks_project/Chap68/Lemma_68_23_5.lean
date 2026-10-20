/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.PuncturedGenerizations
import StacksCheckRecall

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Points.puncturedGenerizations :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S},
    AlgebraicGeometry.AlgebraicSpace.Points X → Set (AlgebraicGeometry.AlgebraicSpace.Points X))

#check (AlgebraicGeometry.AlgebraicSpace.Points.mem_puncturedGenerizations :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    {x x' : AlgebraicGeometry.AlgebraicSpace.Points X},
    x' ∈ AlgebraicGeometry.AlgebraicSpace.Points.puncturedGenerizations x ↔ x' ⤳ x ∧ x' ≠ x)

/- Lemma 68.23.5
The strict generizations of a point of a decent locally Noetherian algebraic space
form a Noetherian, spectral, sober, Jacobson topological space.
-/
@[stacks 0ED2] #check
  (AlgebraicGeometry.AlgebraicSpace.Points.instNoetherianSpace_puncturedGenerizations :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
      [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X]
      (x : AlgebraicGeometry.AlgebraicSpace.Points X),
      TopologicalSpace.NoetherianSpace
        (AlgebraicGeometry.AlgebraicSpace.Points.puncturedGenerizations x))

#check (AlgebraicGeometry.AlgebraicSpace.Points.instSpectralSpace_puncturedGenerizations :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
    [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X]
    (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    SpectralSpace (AlgebraicGeometry.AlgebraicSpace.Points.puncturedGenerizations x))

#check (AlgebraicGeometry.AlgebraicSpace.Points.puncturedGenerizations_sober :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
    [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X]
    {x : AlgebraicGeometry.AlgebraicSpace.Points X},
    T0Space (AlgebraicGeometry.AlgebraicSpace.Points.puncturedGenerizations x) ∧
      QuasiSober (AlgebraicGeometry.AlgebraicSpace.Points.puncturedGenerizations x))

#check (AlgebraicGeometry.AlgebraicSpace.Points.instJacobsonSpace_puncturedGenerizations :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
    [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X]
    (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    JacobsonSpace (AlgebraicGeometry.AlgebraicSpace.Points.puncturedGenerizations x))

