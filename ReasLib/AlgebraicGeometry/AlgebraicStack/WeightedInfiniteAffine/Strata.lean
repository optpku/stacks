/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.RestrictedAction
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer
public import ReasLib.AlgebraicGeometry.RootsOfUnity.GroupScheme
public import ReasLib.CategoryTheory.Fibered.Groupoids.GerbeMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.SmallFunctoriality
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

/-!
# Gerbe strata of the weighted infinite quotient stack

The restricted action quotients give reduced locally closed strata of `[U / 𝔾ₘ]`,
with the stated stabilizers, gerbe structures, partition, and coarseness properties.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.Groupoids.Hom
open AlgebraicGeometry.GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids.Hom
open CartesianMonoidalCategory MonoidalCategory
open scoped AlgebraicGeometry Bicategory CategoryTheory.MonObj MonoidalLeftAction

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine

/-- The quotient stack of the restricted action on a stratum locus. -/
def stratumStack (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : StratumIndex) :
    GroupoidsOver (base k) :=
  GroupoidAlgebraicSpace.SmallQuotient.quotientStack (restrictedActionGroupoid k p hp i)

/-- The quotient stack of each restricted action is an algebraic stack. -/
instance instAlgebraicStackStratumStack (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) (i : StratumIndex) :
    AlgebraicStack (stratumStack k p hp i) := sorry

/-- The quotient of each weighted invariant locus is a reduced algebraic stack. -/
instance instIsReducedStratumStack (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) (i : StratumIndex) :
    AlgebraicStack.IsReduced (stratumStack k p hp i) := sorry

/-- The locus inclusion commutes with the source maps of the action groupoids. -/
theorem stratumGroupoidHom_map_s (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) (i : StratumIndex) :
    (restrictedActionGroupoid k p hp i).s ≫ locusιAsOver k i =
      whiskerLeft (multiplicativeGroup k).X (locusιAsOver k i) ≫ (groupoid k p hp).s := sorry

/-- The locus inclusion commutes with the target maps of the action groupoids. -/
theorem stratumGroupoidHom_map_t (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) (i : StratumIndex) :
    (restrictedActionGroupoid k p hp i).t ≫ locusιAsOver k i =
      whiskerLeft (multiplicativeGroup k).X (locusιAsOver k i) ≫ (groupoid k p hp).t := sorry

/-- The locus inclusion preserves composition in the action groupoids. -/
theorem stratumGroupoidHom_map_c (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) (i : StratumIndex) :
    (restrictedActionGroupoid k p hp i).c ≫
        whiskerLeft (multiplicativeGroup k).X (locusιAsOver k i) =
      GroupoidAlgebraicSpace.composableMap (locusιAsOver k i)
        (whiskerLeft (multiplicativeGroup k).X (locusιAsOver k i))
        (stratumGroupoidHom_map_s k p hp i) (stratumGroupoidHom_map_t k p hp i) ≫
          (groupoid k p hp).c := sorry

/-- The groupoid morphism induced by the equivariant immersion of a stratum locus. -/
def stratumGroupoidHom (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : StratumIndex) :
    GroupoidAlgebraicSpace.Hom (restrictedActionGroupoid k p hp i) (groupoid k p hp) where
  obj := locusιAsOver k i
  arrow := whiskerLeft (multiplicativeGroup k).X (locusιAsOver k i)
  map_s := stratumGroupoidHom_map_s k p hp i
  map_t := stratumGroupoidHom_map_t k p hp i
  map_c := stratumGroupoidHom_map_c k p hp i

/-- The quotient morphism induced by the equivariant immersion of a stratum locus. -/
def stratumι (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : StratumIndex) : stratumStack k p hp i ⟶ stack k p hp :=
  GroupoidAlgebraicSpace.Hom.quotientStackHom (stratumGroupoidHom k p hp i)

/-- The restricted-quotient inclusion of each stratum is an immersion. -/
instance instImmersionStratumι (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : StratumIndex) : Immersion (stratumι k p hp i) := sorry

/-- Pullback of `μ_{p^i}` along the finite stratum locus. -/
def finiteLocusRootsOfUnity (k : Type u) [Field k] (p i : ℕ) (hp : Nat.Prime p) :
    GroupScheme (finiteLocus k i).left :=
  GroupScheme.baseChange
    (@RootsOfUnity.baseChange (p ^ i) ⟨pow_ne_zero i hp.ne_zero⟩ (base k)).toGrp
    (finiteLocus k i).hom

/-- Pullback of `𝔾ₘ[Spec k]` along the origin locus. -/
def infinityLocusMultiplicativeGroup (k : Type u) [Field k] :
    GroupScheme (infinityLocus k).left :=
  GroupScheme.baseChange (𝔾ₘ[base k]).toGrp (infinityLocus k).hom

/-- The stabilizer of the restricted finite-stratum action, as a group scheme over that locus. -/
def finiteLocusStabilizer (k : Type u) [Field k] (p i : ℕ) :
    GroupScheme (finiteLocus k i).left :=
  (Over.iteratedSliceEquiv (finiteLocus k i)).functor.mapGrp.obj
    (GroupoidScheme.stabilizer (restrictedGroupoid k p (StratumIndex.ofNat i)))

/-- The stabilizer of the restricted origin action, as a group scheme over the origin locus. -/
def infinityLocusStabilizer (k : Type u) [Field k] (p : ℕ) :
    GroupScheme (infinityLocus k).left :=
  (Over.iteratedSliceEquiv (infinityLocus k)).functor.mapGrp.obj
    (GroupoidScheme.stabilizer (restrictedGroupoid k p StratumIndex.inf))

/-- On the finite locus, the restricted stabilizer is the pullback of `μ_{p^i}` as group schemes. -/
theorem restrictedStabilizer_iso_rootsOfUnity (k : Type u) [Field k] (p i : ℕ)
    (hp : Nat.Prime p) :
    Nonempty (finiteLocusStabilizer k p i ≅ finiteLocusRootsOfUnity k p i hp) := sorry

/-- On the origin locus, the restricted stabilizer is the pullback of `𝔾ₘ` as group schemes. -/
theorem restrictedStabilizer_iso_multiplicativeGroup (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) :
    Nonempty (infinityLocusStabilizer k p ≅ infinityLocusMultiplicativeGroup k) := sorry

/-- Each finite stratum is a gerbe over a scheme with group `μ_{p^i}`. -/
theorem isGerbeOver_rootsOfUnity (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : ℕ) :
    ∃ (Y : Over (base k))
      (f : stratumStack k p hp (StratumIndex.ofNat i) ⟶ GroupoidsOver.slice Y),
      IsGerbeMorphism (Scheme.fppfTopology.over (base k)) f ∧
        Nonempty (finiteLocusStabilizer k p i ≅ finiteLocusRootsOfUnity k p i hp) := sorry

/-- The infinite stratum is a gerbe over a scheme with group `𝔾ₘ`. -/
theorem isGerbeOver_multiplicativeGroup (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) :
    ∃ (Y : Over (base k))
      (f : stratumStack k p hp StratumIndex.inf ⟶ GroupoidsOver.slice Y),
      IsGerbeMorphism (Scheme.fppfTopology.over (base k)) f ∧
        Nonempty (infinityLocusStabilizer k p ≅ infinityLocusMultiplicativeGroup k) := sorry

/-- The images of the strata partition the points of `[U / 𝔾ₘ]`. -/
theorem isStratification (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    (∀ x : Points (stack k p hp),
        ∃ i : StratumIndex, x ∈ Set.range (Points.map (stratumι k p hp i))) ∧
      Pairwise fun i j : StratumIndex ↦
        Disjoint (Set.range (Points.map (stratumι k p hp i)))
          (Set.range (Points.map (stratumι k p hp j))) := sorry

/-- A reduced locally closed gerbe whose image is a nonempty union of the weighted
strata contains exactly one of these strata. -/
theorem isCoarsest (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (Z : GroupoidsOver (base k)) [AlgebraicStack Z]
    (f : Z ⟶ stack k p hp) [Immersion f] (I : Set StratumIndex)
    (h_reduced : AlgebraicStack.IsReduced Z)
    (h_nonempty : I.Nonempty)
    (h_gerbe : ∃ (S : Over (base k)) (g : Z ⟶ GroupoidsOver.slice S),
      IsGerbeMorphism (Scheme.fppfTopology.over (base k)) g)
    (h_union : Set.range (Points.map f) =
      ⋃ i ∈ I, Set.range (Points.map (stratumι k p hp i))) :
    ∃ i : StratumIndex, I = {i} := sorry

end AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine
