/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BivariantClass
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Cancellation

/-!
# Flat pullback as a bivariant class

A morphism of good algebraic spaces which is flat of
exact relative dimension `r` determines a degree `-(r : ℤ)` bivariant class
whose cap maps are the Chow-level flat pullbacks along cartesian left
verticals.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BivariantClass

variable {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
variable (f : X ⟶ Y) [QuasiSeparated (f ≫ pY)] [LocallyOfFiniteType (f ≫ pY)]

/-- Structure morphisms on a cartesian square agree after composing with
`pY`. -/
theorem structureMorphism_eq {X' Y' : AlgebraicSpace S}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (square : IsPullback i f' f g) :
    f' ≫ g ≫ pY = i ≫ f ≫ pY :=
  sorry

variable (r : ℕ) [Flat f] [RelativeDimension f r]

/-- Chow-level flat pullback along the left vertical of a cartesian square,
using the transferred flatness and relative dimension of `f`. -/
noncomputable def chowFlatPullback_isPullback {X' Y' : AlgebraicSpace S}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (square : IsPullback i f' f g) (k : ℤ) :
    Hom.chowGroup (g ≫ pY) δ k →+ Hom.chowGroup (i ≫ f ≫ pY) δ (k + (r : ℤ)) :=
  -- Local instance justification (proof-local temporary data): Cancellation of the good structure morphism supplies local finite type needed to transfer exact relative dimension.
  letI : LocallyOfFiniteType f := LocallyOfFiniteType.of_comp f pY
  @ChowGroup.flatPullback _ _ _ _ _ _ (g ≫ pY) _ _ (i ≫ f ≫ pY) _ _ δ _ f' r
    (Flat.of_isPullback square inferInstance)
    (RelativeDimension.of_isPullback square inferInstance)
    (structureMorphism_eq pY f i f' g square) k

/-- On a cartesian left vertical already known to be flat of relative
dimension `r`, `chowFlatPullback_isPullback` is `ChowGroup.flatPullback`. -/
theorem chowFlatPullback_isPullback_eq {X' Y' : AlgebraicSpace S}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (square : IsPullback i f' f g) [Flat f'] [RelativeDimension f' r] (k : ℤ) :
    chowFlatPullback_isPullback δ pY f r i f' g square k =
      ChowGroup.flatPullback (g ≫ pY) (i ≫ f ≫ pY) δ f' r
        (structureMorphism_eq pY f i f' g square) k :=
  sorry

/-- Cap family of Chow-level flat pullbacks, reindexed as a degree
`-(r : ℤ)` operation. -/
noncomputable def flatPullbackCapFamily : CapFamily δ pY f (-(r : ℤ)) :=
  fun {X' Y'} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
      [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
      [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
      (square : IsPullback i f' f g) (k : ℤ) ↦
    (castChowGroup δ (i ≫ f ≫ pY)
        (sub_neg_eq_add k (r : ℤ)).symm).comp
      (chowFlatPullback_isPullback δ pY f r i f' g square k)

/-- Unfolding of `flatPullbackCapFamily` as reindexed cartesian flat
pullback. -/
theorem flatPullbackCapFamily_apply {X' Y' : AlgebraicSpace S}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (square : IsPullback i f' f g) (k : ℤ) :
    flatPullbackCapFamily δ pY f r i f' g square k =
      (castChowGroup δ (i ≫ f ≫ pY)
          (sub_neg_eq_add k (r : ℤ)).symm).comp
        (chowFlatPullback_isPullback δ pY f r i f' g square k) :=
  sorry

/-- The flat-pullback cap family is compatible with proper pushforward. -/
theorem flatPullbackCapFamily_map_proper :
    CompatibleWithProperPushforward δ pY f (flatPullbackCapFamily δ pY f r) :=
  sorry

/-- The flat-pullback cap family is compatible with flat pullback. -/
theorem flatPullbackCapFamily_pullback_flat :
    CompatibleWithFlatPullback δ pY f (flatPullbackCapFamily δ pY f r) :=
  sorry

/-- The flat-pullback cap family is compatible with Cartier Gysin. -/
theorem flatPullbackCapFamily_gysin_cartier :
    CompatibleWithCartierGysin δ pY f (flatPullbackCapFamily δ pY f r) :=
  sorry

/-- A flat morphism of good algebraic spaces over `B` of relative dimension
`r` defines a bivariant class of degree `-(r : ℤ)`, whose cap maps are the
flat Chow pullbacks on cartesian base changes. -/
noncomputable def flatPullback : BivariantClass δ pY f (-(r : ℤ)) :=
  ofCap δ pY f (flatPullbackCapFamily δ pY f r)
    (flatPullbackCapFamily_map_proper δ pY f r)
    (flatPullbackCapFamily_pullback_flat δ pY f r)
    (flatPullbackCapFamily_gysin_cartier δ pY f r)

/-- The cap maps of `flatPullback` are the reindexed Chow-level flat
pullbacks. -/
theorem flatPullback_cap {X' Y' : AlgebraicSpace S}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (square : IsPullback i f' f g) (k : ℤ) :
    (flatPullback δ pY f r).cap i f' g square k =
      flatPullbackCapFamily δ pY f r i f' g square k :=
  sorry

/-- On the chosen fibre product `X' = X ×_Y Y'`, the cap of `flatPullback`
is the reindexed Chow-level flat pullback along `pullback.snd f g`. -/
theorem flatPullback_cap_pullback {Y' : AlgebraicSpace S} (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (pullback.fst f g ≫ f ≫ pY)]
    [LocallyOfFiniteType (pullback.fst f g ≫ f ≫ pY)] (k : ℤ) :
    (flatPullback δ pY f r).cap (pullback.fst f g) (pullback.snd f g) g
        (IsPullback.of_hasPullback f g) k =
      (castChowGroup δ (pullback.fst f g ≫ f ≫ pY)
          (sub_neg_eq_add k (r : ℤ)).symm).comp
        (chowFlatPullback_isPullback δ pY f r
          (pullback.fst f g) (pullback.snd f g) g
          (IsPullback.of_hasPullback f g) k) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.BivariantClass
