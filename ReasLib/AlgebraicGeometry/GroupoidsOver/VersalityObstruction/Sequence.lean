/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalityObstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Infinite first-order thickenings detecting failure of versality

On a locally Noetherian base, a groupoid fibration with (RS*) that fails to be
versal at infinitely many pairwise non-specializing finite type points of an
affine finite-type source admits an infinite chain of first-order thickenings
with residue-field kernels and no local retractions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open RingedSpace.Module
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Existence of an open neighbourhood `W ⊆ T` of the image of `u` and a
morphism `β : y|_W ⟶ x` such that the restriction `ρ` of `φ : x ⟶ y` to
`U ∩ W` satisfies `ρ ≫ β` equal to the canonical morphism `x|_{U ∩ W} ⟶ x`. -/
def existsLocalRetraction {S U T : Scheme.{u}} {X : GroupoidsOver S}
    {hU : U ⟶ S} {hT : T ⟶ S} {i : U ⟶ T} (hi : i ≫ hT = hU)
    {x y : X.total} (hx : X.p.obj x = Over.mk hU) (hy : X.p.obj y = Over.mk hT)
    (φ : x ⟶ y) (u : U) : Prop :=
  ∃ (W : T.Opens), i.base u ∈ W ∧
    ∃ (β : (Chosen.reindexObj X.p (Over.homMk W.ι rfl : Over.mk (W.ι ≫ hT) ⟶ Over.mk hT) ⟨y, hy⟩).1 ⟶ x)
      (ρ : (Chosen.reindexObj X.p (Over.homMk (i ⁻¹ᵁ W).ι rfl : Over.mk ((i ⁻¹ᵁ W).ι ≫ hU) ⟶ Over.mk hU) ⟨x, hx⟩).1 ⟶
        (Chosen.reindexObj X.p (Over.homMk W.ι rfl : Over.mk (W.ι ≫ hT) ⟶ Over.mk hT) ⟨y, hy⟩).1),
      X.p.IsHomLift (Over.homMk (i ∣_ W) (by
            change (i ∣_ W) ≫ (W.ι ≫ hT) = (i ⁻¹ᵁ W).ι ≫ hU
            rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hi]) :
              Over.mk ((i ⁻¹ᵁ W).ι ≫ hU) ⟶ Over.mk (W.ι ≫ hT)) ρ ∧
        ρ ≫ Chosen.cartesianHom X.p (Over.homMk W.ι rfl : Over.mk (W.ι ≫ hT) ⟶ Over.mk hT) ⟨y, hy⟩ =
          Chosen.cartesianHom X.p (Over.homMk (i ⁻¹ᵁ W).ι rfl : Over.mk ((i ⁻¹ᵁ W).ι ≫ hU) ⟶ Over.mk hU) ⟨x, hx⟩ ≫ φ ∧
        ρ ≫ β =
          Chosen.cartesianHom X.p (Over.homMk (i ⁻¹ᵁ W).ι rfl : Over.mk ((i ⁻¹ᵁ W).ι ≫ hU) ⟶ Over.mk hU) ⟨x, hx⟩

/-- A local retraction exists exactly when an open neighbourhood of the image
point admits a morphism back whose composite with the restricted original
morphism is the canonical restriction morphism. -/
theorem existsLocalRetraction_iff {S U T : Scheme.{u}} {X : GroupoidsOver S}
    {hU : U ⟶ S} {hT : T ⟶ S} {i : U ⟶ T} (hi : i ≫ hT = hU)
    {x y : X.total} (hx : X.p.obj x = Over.mk hU) (hy : X.p.obj y = Over.mk hT)
    (φ : x ⟶ y) (u : U) :
    existsLocalRetraction hi hx hy φ u ↔
      ∃ (W : T.Opens), i.base u ∈ W ∧
        ∃ (β : (Chosen.reindexObj X.p (Over.homMk W.ι rfl : Over.mk (W.ι ≫ hT) ⟶ Over.mk hT) ⟨y, hy⟩).1 ⟶ x)
          (ρ : (Chosen.reindexObj X.p (Over.homMk (i ⁻¹ᵁ W).ι rfl : Over.mk ((i ⁻¹ᵁ W).ι ≫ hU) ⟶ Over.mk hU) ⟨x, hx⟩).1 ⟶
            (Chosen.reindexObj X.p (Over.homMk W.ι rfl : Over.mk (W.ι ≫ hT) ⟶ Over.mk hT) ⟨y, hy⟩).1),
          X.p.IsHomLift (Over.homMk (i ∣_ W) (by
            change (i ∣_ W) ≫ (W.ι ≫ hT) = (i ⁻¹ᵁ W).ι ≫ hU
            rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hi]) :
              Over.mk ((i ⁻¹ᵁ W).ι ≫ hU) ⟶ Over.mk (W.ι ≫ hT)) ρ ∧
            ρ ≫ Chosen.cartesianHom X.p (Over.homMk W.ι rfl : Over.mk (W.ι ≫ hT) ⟶ Over.mk hT) ⟨y, hy⟩ =
              Chosen.cartesianHom X.p (Over.homMk (i ⁻¹ᵁ W).ι rfl : Over.mk ((i ⁻¹ᵁ W).ι ≫ hU) ⟶ Over.mk hU) ⟨x, hx⟩ ≫ φ ∧
            ρ ≫ β =
              Chosen.cartesianHom X.p (Over.homMk (i ⁻¹ᵁ W).ι rfl : Over.mk ((i ⁻¹ᵁ W).ι ≫ hU) ⟶ Over.mk hU) ⟨x, hx⟩ :=
  Iff.rfl

/-- Over a locally Noetherian base, an object of a groupoid fibration with
(RS*) that is not versal at pairwise non-specializing finite type points of an
affine finite-type source admits a compatible infinite sequence of first-order
thickenings with successive residue-field kernels and no local retractions.
The index `n` labels the `(n + 1)`st thickening: the initial kernel is supported
at `u 0`, and the kernel of `step n` is supported at the image of `u (n + 1)`. -/
@[stacks 0G2S]
theorem exists_firstOrderThickeningSequence_of_not_isVersalAt
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] {U : Scheme.{u}} [IsAffine U]
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u : ℕ → U)
    (hu : ∀ n, IsFiniteTypePoint (u n))
    (hns : ∀ ⦃n m⦄, n ≠ m → ¬ Specializes (u n) (u m))
    (h : ∀ n, ¬ IsVersalAt hU x hx (u n)) :
    ∃ (Useq : ℕ → Scheme.{u}) (hUseq : ∀ n, Useq n ⟶ S)
      (iU : ∀ n, U ⟶ Useq n) (hiU : ∀ n, iU n ≫ hUseq n = hU)
      (step : ∀ n, Useq n ⟶ Useq (n + 1))
      (hstep : ∀ n, step n ≫ hUseq (n + 1) = hUseq n)
      (h_comp : ∀ n, iU (n + 1) = iU n ≫ step n)
      (xseq : ℕ → X.total)
      (hxseq : ∀ n, X.p.obj (xseq n) = Over.mk (hUseq n))
      (Φ : ∀ n, x ⟶ xseq n) (φ : ∀ n, xseq n ⟶ xseq (n + 1)),
      (∀ n, X.p.IsHomLift (Over.homMk (iU n) (hiU n) : Over.mk hU ⟶ Over.mk (hUseq n)) (Φ n)) ∧
        (∀ n, X.p.IsHomLift (Over.homMk (step n) (hstep n) : Over.mk (hUseq n) ⟶ Over.mk (hUseq (n + 1))) (φ n)) ∧
          (∀ n, Φ (n + 1) = Φ n ≫ φ n) ∧
            (∀ n, IsFirstOrderThickening (iU n)) ∧
              Nonempty ((iU 0).ker.toModule ≅
                Scheme.Modules.residueFieldSkyscraper ((iU 0).base (u 0))) ∧
                (∀ n, IsFirstOrderThickening (step n)) ∧
                  (∀ n, Nonempty ((step n).ker.toModule ≅
                    Scheme.Modules.residueFieldSkyscraper
                      ((step n).base ((iU n).base (u (n + 1)))))) ∧
                    ∀ n, ¬ existsLocalRetraction (hiU n) hx (hxseq n) (Φ n) (u n) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
