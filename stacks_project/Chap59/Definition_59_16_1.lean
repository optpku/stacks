/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.Canonical
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

/- Definition 59.16.1 (1): descent data for quasi-coherent sheaves along a
family of scheme morphisms with fixed target. -/
@[stacks 03O7] #check
  (@AlgebraicGeometry.Scheme.QCoh.DescentData :
    {I : Type v} → {S : Scheme.{u}} →
      (X : I → Scheme.{u}) → ((i : I) → X i ⟶ S) →
        Type (max (u + 1) v))

/- Definition 59.16.1 (2): effectivity of a quasi-coherent descent datum. -/
@[stacks 03O7] #check
  (@AlgebraicGeometry.Scheme.QCoh.DescentData.IsEffective :
    ∀ {I : Type v} {S : Scheme.{u}}
      {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S},
      AlgebraicGeometry.Scheme.QCoh.DescentData X f → Prop)

/- Companion bridge: effectivity is equivalent to being isomorphic to the
canonical descent datum of a quasi-coherent sheaf on the target. -/
#check (@AlgebraicGeometry.Scheme.QCoh.DescentData.isEffective_iff :
  ∀ {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (D : AlgebraicGeometry.Scheme.QCoh.DescentData X f),
      D.IsEffective ↔
        ∃ F : AlgebraicGeometry.Scheme.QCoh S,
          Nonempty (AlgebraicGeometry.Scheme.QCoh.DescentData.canonical X f F ≅ D))
