/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Coproduct

open CategoryTheory

universe u v

#check (AlgebraicGeometry.Scheme.DescentData.restrictCoproduct :
  ∀ {I : Type v} [Small.{u} I] {S : AlgebraicGeometry.Scheme.{u}}
    (X : I → AlgebraicGeometry.Scheme.{u}) (f : ∀ i, X i ⟶ S),
    AlgebraicGeometry.Scheme.DescentData
        (AlgebraicGeometry.Scheme.DescentData.coproductFamily X)
        (AlgebraicGeometry.Scheme.DescentData.coproductArrow X f) ⥤
      AlgebraicGeometry.Scheme.DescentData X f)
