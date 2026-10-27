/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Definition 77.3.1 (1): in Situation 77.2.1, a finite type quasi-coherent module is
pure above `y` when none of the equivalent impurity conditions of Lemma 77.2.5 hold. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsPureAlong :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
      [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType]
      (y : Points Y), Prop)

/- Definition 77.3.1 (2): a finite type quasi-coherent module is universally pure above
`y` when it has no impurity above `y`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsUniversallyPureAlong :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
      [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType]
      (y : Points Y), Prop)

/- Definition 77.3.1 (3): an algebraic space is pure above `y` when its structure sheaf
is pure above `y`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsPureAlong :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [FiniteType f] [Decent f] (y : Points Y), Prop)

/- Definition 77.3.1 (4): a finite type quasi-coherent module is universally pure
relative to `Y` when it is universally pure above every point of `Y`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsUniversallyPureOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
      [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType], Prop)

/- Definition 77.3.1 (5): a finite type quasi-coherent module is pure relative to `Y`
when it is pure above every point of `Y`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsPureOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
      [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType], Prop)

/- Definition 77.3.1 (6): an algebraic space is pure relative to `Y` when its structure
sheaf is pure relative to `Y`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsPureOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [FiniteType f] [Decent f], Prop)
