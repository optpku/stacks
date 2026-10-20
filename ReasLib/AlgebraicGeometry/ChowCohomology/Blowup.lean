/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.ProperPushforward
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle
public import ReasLib.AlgebraicGeometry.ChowCohomology.FirstChern
public import ReasLib.AlgebraicGeometry.ChowCohomology.Restriction
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Cartier
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.OverField
public import ReasLib.AlgebraicGeometry.Scheme.K0.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field
public import ReasLib.Topology.KrullDimension.PureCodimension

/-!
# Chow classes of blowups

This file records the exceptional-cycle relation for a blowup of a smooth projective scheme
along a smooth center whose conormal class extends in `K₀`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

set_option maxHeartbeats 800000 in
/-- For a positive pure-codimension smooth center whose conormal `K₀` class extends from the
ambient smooth projective scheme, a specified refined Gysin class admits one exceptional
Chow class satisfying both the exceptional-divisor product relation and the exceptional
pushforward relation. -/
theorem existsBlowupExceptionalCycle
    {k : Type u} [Field k] {X X' : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom]
    (I : X.left.IdealSheafData) [Smooth (I.subschemeι ≫ X.hom)]
    (b : X' ⟶ X) [IsBlowup b.left I] (r : ℕ) (hr : 0 < r)
    (hcodim : TopologicalSpace.HasPureCodimension (I.support : Set X.left) r)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r
      (Scheme.Hom.conormalSheaf I.subschemeι)]
    (hK₀ : ∃ α : Scheme.K0 X.left,
      Scheme.K0.pullback I.subschemeι α =
        Scheme.VectorBundleK0.toK0 I.subscheme
          (ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.IsFiniteLocallyFree : ObjectProperty I.subscheme.Modules)
            ⟨Scheme.Hom.conormalSheaf I.subschemeι,
              Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
                r (Scheme.Hom.conormalSheaf I.subschemeι)⟩))
    (centerGysin : BivariantClass (fun _ ↦ 0)
      (overHom (I.subschemeι ≫ X.hom) X.hom I.subschemeι rfl) (r : ℤ))
    (centerGysin_fundamental : ∀ n : ℤ,
      centerGysin.cap (𝟙 _) (overHom (I.subschemeι ≫ X.hom) X.hom I.subschemeι rfl)
          (𝟙 _) IsPullback.of_id_fst n
          (@chowClass X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n
            (@CycleGroup.fundamental X.left
              (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)) =
        @chowClass I.subscheme
          (LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ X.hom))
          ((I.subschemeι ≫ X.hom).relativeDimensionFunction (fun _ ↦ 0))
          inferInstance (n - (r : ℤ))
          (@CycleGroup.fundamental I.subscheme
            (LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ X.hom))
            ((I.subschemeι ≫ X.hom).relativeDimensionFunction (fun _ ↦ 0))
            (n - (r : ℤ)))) :
    ∃ θ : ChowCohomology.degree (fun _ ↦ 0) X'.hom ((r : ℤ) - 1),
      DirectSum.of (ChowCohomology.degree (fun _ ↦ 0) X'.hom) (r : ℤ)
          (ChowCohomology.restrictDegree (fun _ ↦ 0) b (r : ℤ)
            (BivariantClass.properPushforwardToTarget (fun _ ↦ 0)
              (overHom (I.subschemeι ≫ X.hom) X.hom I.subschemeι rfl) (r : ℤ)
              centerGysin)) =
        DirectSum.of (ChowCohomology.degree (fun _ ↦ 0) X'.hom)
          (1 + ((r : ℤ) - 1))
          (ChowCohomology.mul (fun _ ↦ 0) X'.hom
            (ChowCohomology.firstChernClass (fun _ ↦ 0) X'.hom
              (I.comap b.left).associatedSheaf) θ) ∧
        ∀ n : ℤ,
          ChowGroup.map (fun _ ↦ 0)
              (Over.mk ((I.comap b.left).subschemeι ≫ X'.hom))
              (Over.mk (I.subschemeι ≫ X.hom))
              (exceptionalProjectionOver I b) ((n - ((r : ℤ) - 1)) - 1)
              (ChowGroup.cartierGysin (fun _ ↦ 0) X' (I.comap b.left)
                (n - ((r : ℤ) - 1))
                (θ.cap (𝟙 X') (𝟙 X') (𝟙 X') IsPullback.of_id_snd n
                  (@chowClass X'.left
                    (LocallyOfFiniteType.isLocallyNoetherian X'.hom)
                    (X'.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n
                    (@CycleGroup.fundamental X'.left
                      (LocallyOfFiniteType.isLocallyNoetherian X'.hom)
                      (X'.hom.relativeDimensionFunction (fun _ ↦ 0)) n)))) =
            @chowClass I.subscheme
              (LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ X.hom))
              ((I.subschemeι ≫ X.hom).relativeDimensionFunction (fun _ ↦ 0))
              inferInstance ((n - ((r : ℤ) - 1)) - 1)
              (@CycleGroup.fundamental I.subscheme
                (LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ X.hom))
                ((I.subschemeι ≫ X.hom).relativeDimensionFunction (fun _ ↦ 0))
                ((n - ((r : ℤ) - 1)) - 1)) := sorry

end AlgebraicGeometry.IsBlowup
