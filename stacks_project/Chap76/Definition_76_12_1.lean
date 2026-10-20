/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.InfinitesimalNeighbourhood
public import stacks_project.Chap76.Definition_76_12_1_Neighbourhood
import StacksCheckRecall

open CategoryTheory

universe u

/- The source uses orders `n ≥ 1`; the natural-number indexed construction
also defines order zero. First order is exactly `n = 1`. -/

/- Definition 76.12.1: if `i : Z ⟶ X` is an immersion of algebraic spaces, then
its `n`th infinitesimal neighbourhood is the closed subspace of the coborder
open cut out by the `(n + 1)`st power of the coborder kernel ideal. The case
`n = 1` is the first-order infinitesimal neighbourhood, and `fromSource i n` is
the `n`th-order thickening of `Z` over `X`. -/
@[stacks 05ZV] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.space :
    {S : AlgebraicGeometry.Scheme.{u}} →
      {Z X : AlgebraicGeometry.AlgebraicSpace S} → (i : Z ⟶ X) →
        [AlgebraicGeometry.AlgebraicSpace.IsImmersion i] → ℕ →
          AlgebraicGeometry.AlgebraicSpace S)

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood
open SheafOfModules.RingedSite

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

#check (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.ideal_eq_pow i :
  ∀ n : ℕ, ideal i n = (Hom.idealSheafSubobject (IsImmersion.liftCoborder i)).pow (n + 1))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.ideal_apply i :
  ∀ (n : ℕ) (U : (smallEtaleSite (IsImmersion.coborderRange i).X)ᵒᵖ)
    [IsAffine ((smallEtaleToScheme (IsImmersion.coborderRange i).X).obj U.unop)],
    IdealSheaf.sections (Modules.toCommSubobject (ideal i n)) U =
      IdealSheaf.sections
        (Modules.toCommSubobject (Hom.idealSheafSubobject (IsImmersion.liftCoborder i)))
        U ^ (n + 1))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.fromSource i :
  ∀ n : ℕ, Z ⟶ space i n)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.toAmbient i :
  ∀ n : ℕ, space i n ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.fromSource_toAmbient i :
  ∀ n : ℕ, fromSource i n ≫ toAmbient i n = i)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.fromSource_isNthOrderThickening i :
  ∀ n : ℕ, IsNthOrderThickening n (fromSource i n))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.fromSource_isFirstOrderThickening i :
  IsFirstOrderThickening (fromSource i 1))
