/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Distance.Properties

open Set TopologicalSpace
open scoped AlgebraicGeometry

universe u

open AlgebraicGeometry AlgebraicGeometry.Scheme

/- Lemma 52.18.1 (1): the distance from a point `y` to a closed subset `Z` of a
Noetherian scheme is zero exactly when `y ∈ Z`. -/
@[stacks 0EIY] #check (AlgebraicGeometry.Scheme.distanceTo_eq_zero_iff :
    ∀ {Y : AlgebraicGeometry.Scheme.{u}} [IsNoetherian Y] (Z : Closeds Y) (y : Y),
      Y.distanceTo Z y = 0 ↔ y ∈ Z)

/- Lemma 52.18.1 (2): every sublevel set of the distance to `Z` is stable under
specialization. -/
@[stacks 0EIY] #check (AlgebraicGeometry.Scheme.stableUnderSpecialization_distanceTo_le :
    ∀ {Y : AlgebraicGeometry.Scheme.{u}} [IsNoetherian Y] (Z : Closeds Y) (k : ℕ∞),
      StableUnderSpecialization {y : Y | Y.distanceTo Z y ≤ k})

/- Lemma 52.18.1 (3): at a point `z` of the reduced closure of `y` whose image lies in
`Z`, the dimension of the local ring of that closure is at least the distance from `y` to
`Z`. -/
@[stacks 0EIY] #check (AlgebraicGeometry.Scheme.distanceTo_le_ringKrullDim_pointClosure_stalk :
    ∀ {Y : AlgebraicGeometry.Scheme.{u}} [IsNoetherian Y] (Z : Closeds Y) (y : Y)
      (z : PointClosure.scheme y) (hz : (PointClosure.ι y) z ∈ Z),
      (Y.distanceTo Z y : WithBot ℕ∞) ≤
        ringKrullDim ((PointClosure.scheme y).presheaf.stalk z))

/- Lemma 52.18.1 (4): if `δ` is a dimension function and `δmax` is its maximum on `Z`,
then the distance to `Z` is bounded below by `δ y - δmax`. -/
@[stacks 0EIY] #check (AlgebraicGeometry.Scheme.dimensionFunction_sub_max_le_distanceTo :
    ∀ {Y : AlgebraicGeometry.Scheme.{u}} [IsNoetherian Y] (Z : Closeds Y) (δ : Y → ℤ)
      [IsDimensionFunction δ] (δmax : ℤ)
      (hδmax : IsGreatest (δ '' (Z : Set Y)) δmax) (y : Y),
      ((δ y - δmax).toNat : ℕ∞) ≤ Y.distanceTo Z y)

/- Lemma 52.18.1 (5): for the spectrum of a catenary Noetherian local ring, distance to
the closed point equals the dimension of the closure of the given point. -/
@[stacks 0EIY] #check (AlgebraicGeometry.Scheme.distanceTo_closedPoint_eq_topologicalKrullDim_closure :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [IsCatenaryRing A] (y : PrimeSpectrum A),
      (distanceTo (Spec (.of A))
        (⟨({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)),
          IsLocalRing.isClosed_singleton_closedPoint A⟩ : Closeds (Spec (.of A))) y :
        WithBot ℕ∞) = topologicalKrullDim (closure ({y} : Set (PrimeSpectrum A))))

/- Lemma 52.18.1 (6): restriction to an open subscheme can only increase the distance to
the restricted closed subset. -/
@[stacks 0EIY] #check (AlgebraicGeometry.Scheme.distanceTo_le_open :
    ∀ {Y : AlgebraicGeometry.Scheme.{u}} [IsNoetherian Y] (Z : Closeds Y) (U : Y.Opens) (y : U),
      Y.distanceTo Z (U.ι y) ≤
        @distanceTo U.toScheme (instIsNoetherianRestrictOfIsNoetherian U)
          (Z.preimage U.ι.continuous) y)

/- Lemma 52.18.1 (7): on a catenary Noetherian scheme, the distance of an immediate
generalization of `y` to `Z` is at most the distance of `y` to `Z` plus one. -/
@[stacks 0EIY] #check (AlgebraicGeometry.Scheme.distanceTo_le_add_one_of_immediateSpecialization :
    ∀ {Y : AlgebraicGeometry.Scheme.{u}} [IsNoetherian Y] [CatenarySpace Y] (Z : Closeds Y)
      {y' y : Y} (h : IsImmediateSpecialization y' y),
      Y.distanceTo Z y' ≤ Y.distanceTo Z y + 1)

/- Lemma 52.18.1 (8): in a catenary Noetherian scheme, a zigzag with `k` immediate
left specializations, starting at a point of `Z`, ends at distance at most `k` from `Z`. -/
@[stacks 0EIY] #check (AlgebraicGeometry.Scheme.distanceTo_le_of_specialization_pattern :
    ∀ {Y : AlgebraicGeometry.Scheme.{u}} [IsNoetherian Y] [CatenarySpace Y] (Z : Closeds Y) (k : ℕ)
      (y : Fin (k + 1) → Y) (y' : Fin k → Y) (hy0 : y 0 ∈ Z)
      (hleft : ∀ i : Fin k, IsImmediateSpecialization (y' i) (y i.castSucc))
      (hright : ∀ i : Fin k, y' i ⤳ y i.succ),
      Y.distanceTo Z (y (Fin.last k)) ≤ k)
