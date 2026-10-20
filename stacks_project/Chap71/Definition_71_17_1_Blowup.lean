/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.RelativeProj
public import stacks_project.Chap67.Lemma_67_13_1_Correspondence
public import stacks_project.Chap71.Definition_71_17_1_Rees
public import stacks_project.Chap71.Lemma_71_6_12_Pullback
public import stacks_project.Chap71.Lemma_71_11_11_Twist

/-!
# Blowups of algebraic spaces in quasi-coherent ideal sheaves

A chosen blowup of an algebraic space `X` in a quasi-coherent ideal sheaf `I`
is a relative projective spectrum of the Rees algebra of `I`. The center is the
closed subspace cut out by `I`, and the exceptional divisor is the inverse image
of that center.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Blowup :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) → (I : IdealSubobject X) →
      [IsQuasiCoherent I] → Type (u + 2))

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.reesTwist :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → {I : IdealSubobject X} →
      [IsQuasiCoherent I] → Blowup X I →
        RelativeProj.Twist (reesAlgebra I) (reesDegreePieces I))

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.of :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → {I : IdealSubobject X} →
      [IsQuasiCoherent I] → RelativeProj.Twist (reesAlgebra I) (reesDegreePieces I) →
        Blowup X I)

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.space :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → {I : IdealSubobject X} →
      [IsQuasiCoherent I] → Blowup X I → AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.hom :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → {I : IdealSubobject X} →
      [IsQuasiCoherent I] → (π : Blowup X I) → (π.space ⟶ X))

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.toOver :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → {I : IdealSubobject X} →
      [IsQuasiCoherent I] → Blowup X I → Over X)

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.center :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → (I : IdealSubobject X) →
      [IsQuasiCoherent I] → ClosedSubspace X)

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.exceptionalDivisor :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → {I : IdealSubobject X} →
      [IsQuasiCoherent I] → (π : Blowup X I) → ClosedSubspace π.space)

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.along :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → (Z : ClosedSubspace X) →
      Type (u + 2))
