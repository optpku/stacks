/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood

universe u

#check (AlgebraicGeometry.Scheme.EtaleNeighborhood :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) (s : S), Type (u + 1))

#check (AlgebraicGeometry.Scheme.EtaleNeighborhood.Hom :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {s : S},
    AlgebraicGeometry.Scheme.EtaleNeighborhood S s →
      AlgebraicGeometry.Scheme.EtaleNeighborhood S s → Type u)

#check (AlgebraicGeometry.Scheme.EtaleNeighborhood.IsElementary :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {s : S},
    AlgebraicGeometry.Scheme.EtaleNeighborhood S s → Prop)
