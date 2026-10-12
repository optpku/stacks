/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation.Diagram

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/-! The source compatibility module re-exports the shared diagram API. -/

#check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram :
    {S : Scheme.{u}} → {X B Bi : AlgebraicSpace S} →
      (X ⟶ B) → (B ⟶ Bi) → Type (u + 1))

#check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram.mk :
    {S : Scheme.{u}} → {X B Bi : AlgebraicSpace S} →
      {f : X ⟶ B} → {π : B ⟶ Bi} →
      (W : AlgebraicSpace S) → (toW : X ⟶ W) → (toBi : W ⟶ Bi) →
      CommSq toW f toBi π →
        AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram f π)

#check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram.W :
    {S : Scheme.{u}} → {X B Bi : AlgebraicSpace S} →
      {f : X ⟶ B} → {π : B ⟶ Bi} →
      AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram f π →
        AlgebraicSpace S)

#check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram.toW :
    {S : Scheme.{u}} → {X B Bi : AlgebraicSpace S} →
      {f : X ⟶ B} → {π : B ⟶ Bi} →
      (D : AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram f π) →
        X ⟶ D.W)

#check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram.toBi :
    {S : Scheme.{u}} → {X B Bi : AlgebraicSpace S} →
      {f : X ⟶ B} → {π : B ⟶ Bi} →
      (D : AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram f π) →
        D.W ⟶ Bi)

#check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram.comm :
    {S : Scheme.{u}} → {X B Bi : AlgebraicSpace S} →
      {f : X ⟶ B} → {π : B ⟶ Bi} →
      (D : AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram f π) →
        CommSq D.toW f D.toBi π)
