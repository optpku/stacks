/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Cotangent
import StacksCheckRecall

@[expose] public section

open CategoryTheory DerivedCategory
open AlgebraicGeometry AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening AlgebraicGeometry.RingedSpace.Thickening.Solution
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

universe u

/- Lemma 92.21.1 In the first-order deformation problem, the canonical Ext² obstruction
vanishes exactly when a solution exists; solution classes form a torsor under Ext¹,
and compatible automorphisms are canonically identified with Ext⁰. -/
@[stacks 08UZ] #check
  (AlgebraicGeometry.RingedSpace.Thickening.existenceObstruction_eq_zero_iff :
    ∀ {S S' X : RingedSpace.{u}} (t : S ⟶ S') [IsFirstOrderThickening t]
      (f : X ⟶ S) (G : X.Modules) (c : Hom.idealModule t ⟶ (f _*).obj G),
      existenceObstruction t f G c = 0 ↔ Nonempty (Solution t f G c))

#check
  (AlgebraicGeometry.RingedSpace.Thickening.Solution.derivedAddTorsor :
    ∀ {S S' X : RingedSpace.{u}} (t : S ⟶ S') [IsFirstOrderThickening t]
      (f : X ⟶ S) (G : X.Modules) (c : Hom.idealModule t ⟶ (f _*).obj G),
      (S0 : Solution t f G c) →
        AddTorsor (Ext⁽(1 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G))
          (IsoClass t f G c))

#check
  (AlgebraicGeometry.RingedSpace.Thickening.isoClassDerivedEquiv :
    ∀ {S S' X : RingedSpace.{u}} (t : S ⟶ S') [IsFirstOrderThickening t]
      (f : X ⟶ S) (G : X.Modules) (c : Hom.idealModule t ⟶ (f _*).obj G),
      (S0 : Solution t f G c) →
        Ext⁽(1 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G) ≃ IsoClass t f G c)

#check
  (AlgebraicGeometry.RingedSpace.Thickening.autEquiv :
    ∀ {S S' X : RingedSpace.{u}} (t : S ⟶ S') [IsFirstOrderThickening t]
      (f : X ⟶ S) (G : X.Modules) (c : Hom.idealModule t ⟶ (f _*).obj G),
      (sol : Solution t f G c) →
        Ext⁽(0 : ℤ)⁾(derived f, (DerivedCategory.singleFunctor X.Modules 0).obj G) ≃
          Solution.Fitting sol sol)
