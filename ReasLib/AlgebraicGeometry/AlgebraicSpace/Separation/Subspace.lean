/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace

/-!
# Quasi-separated structure morphisms of subspaces

Open and closed subspaces inherit quasi-separated structure morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure morphism of an open subspace of a quasi-separated morphism is
quasi-separated. -/
def quasiSeparated_openSubspace_comp {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (U : OpenSubspace X) (f : X ⟶ B)
    [QuasiSeparated f] : QuasiSeparated (U.ι ≫ f) :=
  @quasiSeparated_comp S U.X X B U.ι f
    (@QuasiSeparated.of_separated S U.X X U.ι
      (@Separated.of_mono S U.X X U.ι U.spec.2)) inferInstance

/-- The structure morphism of a closed subspace of a quasi-separated morphism is
quasi-separated. -/
def quasiSeparated_closedSubspace_comp {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (W : ClosedSubspace X) (f : X ⟶ B)
    [QuasiSeparated f] : QuasiSeparated (W.ι ≫ f) :=
  @quasiSeparated_comp S W.X X B W.ι f
    (@QuasiSeparated.of_separated S W.X X W.ι
      (@Separated.of_mono S W.X X W.ι W.spec.2)) inferInstance

end AlgebraicGeometry.AlgebraicSpace
