/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap82.Lemma_82_28_1_Chern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern

/-!
# First Chern class of an invertible module

In Situation 82.2.1, the degree-1 constant-rank Chern class of an invertible
`𝒪_X`-module equals the operational first Chern identity class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Invertible `𝒪_X`-modules are finite locally free of rank one. -/
instance instIsFiniteLocallyFreeOfRank_one_of_isInvertibleObject
    {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 L :=
  sorry

/-- Invertible `𝒪_X`-modules elaborate as finite locally free of rank `0 + 1`,
matching the rank hypothesis of `degree` at `q = 0`. -/
instance instIsFiniteLocallyFreeOfRank_succ_zero_of_isInvertibleObject
    {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] :
    SheafOfModules.IsFiniteLocallyFreeOfRank (0 + 1) L :=
  instIsFiniteLocallyFreeOfRank_one_of_isInvertibleObject L

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
namespace ConstantRankChern

/-- Lemma 82.28.3: In Situation 82.2.1 let `X / B` be good. Let `L` be an
invertible `𝒪_X`-module. The first Chern class of `L` on `X` of Definition
82.28.2 is equal to the bivariant class of Lemma 82.26.4. -/
@[stacks 0ES0]
theorem degree_one_eq_operational
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules) [isInvertibleObject L] :
    degree f δ L 0 1 le_rfl = OperationalFirstChern.degree f δ L :=
  sorry

/-- Cap actions of the degree-1 constant-rank Chern class of an invertible
`𝒪_X`-module and of the operational first Chern class agree on every good test. -/
theorem degree_one_cap_eq_operational
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules) [isInvertibleObject L]
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (degree f δ L 0 1 le_rfl).cap g k =
      (OperationalFirstChern.degree f δ L).cap g k :=
  sorry

end ConstantRankChern
end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
