/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.RelativeProj
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Rees
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

/- Definition 71.17.1: for a scheme `S`, an algebraic space `X` over `S`, and a
quasi-coherent ideal sheaf `I ⊂ 𝒪_X` with corresponding closed subspace `Z`, the
blowing up of `X` along `Z` (equivalently, the blowing up of `X` in `I`) is the
morphism `b : Proj_X (⊕_{n ≥ 0} I ^ n) ⟶ X` packaged as a chosen
`Blowup X I`; its exceptional divisor is `b⁻¹(Z)`, and `Z` is the center. -/
@[stacks 085Q] #check (AlgebraicGeometry.AlgebraicSpace.Blowup :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) → (I : IdealSubobject X) →
      [IsQuasiCoherent I] → Type (u + 2))

#check (AlgebraicGeometry.AlgebraicSpace.reesAlgebra :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → (I : IdealSubobject X) →
      [IsQuasiCoherent I] → GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X) ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.center :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → (I : IdealSubobject X) →
      [IsQuasiCoherent I] → ClosedSubspace X)

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.exceptionalDivisor :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → {I : IdealSubobject X} →
      [IsQuasiCoherent I] → (π : Blowup X I) → ClosedSubspace π.space)

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.along :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → (Z : ClosedSubspace X) →
      Type (u + 2))
