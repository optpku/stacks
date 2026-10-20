/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian

/-!
# Quasi-finiteness at a point and fibers

This file relates finite-type quasi-finiteness at a point to the topology of the corresponding
scheme-theoretic fiber and to affine-local ring maps.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- For a locally finite type morphism, finite-type quasi-finiteness at a point is equivalent to
the point being isolated in its fiber, to the corresponding closed-point and specialization
criterion, and to finite-type quasi-finiteness for every compatible affine presentation. -/
theorem FiniteType.QuasiFiniteAt.fiberTFAE [LocallyOfFiniteType f] (x : X) :
    List.TFAE
      [ FiniteType.QuasiFiniteAt f x
      , IsOpen ({f.asFiber x} : Set (f.fiber (f x)))
      , f.asFiber x ∈ closedPoints (f.fiber (f x)) ∧
          ∀ x' : f.fiber (f x), x' ≠ f.asFiber x → ¬ Specializes x' (f.asFiber x)
      , ∀ ⦃U : X.Opens⦄, ∀ hU : IsAffineOpen U,
          ∀ ⦃V : S.Opens⦄, ∀ hV : IsAffineOpen V, ∀ e : U ≤ f ⁻¹ᵁ V,
            ∀ q : PrimeSpectrum (Γ(X, U)), hU.fromSpec q = x →
              (CommRingCat.Hom.hom (f.appLE V U e)).FiniteType ∧
                (CommRingCat.Hom.hom (f.appLE V U e)).QuasiFiniteAt q.asIdeal
      ] := sorry

/-- A scheme-theoretic fiber is finite whenever its underlying point-set preimage is finite. -/
theorem finite_fiber_of_finite_preimage_singleton (s : S)
    (hs : Set.Finite (f ⁻¹' ({s} : Set S))) :
    Finite (f.fiber s) := sorry

/-- A finite fiber of a locally finite type morphism has the discrete topology. -/
theorem discreteTopology_fiber_of_finite_preimage_singleton [LocallyOfFiniteType f] (s : S)
    (hs : Set.Finite (f ⁻¹' ({s} : Set S))) :
    DiscreteTopology (f.fiber s) := sorry

/-- A locally finite type morphism with finite point-set fiber over `s` is finite-type
quasi-finite at every point lying over `s`. -/
theorem FiniteType.QuasiFiniteAt.of_finite_preimage_singleton [LocallyOfFiniteType f]
    (s : S) (hs : Set.Finite (f ⁻¹' ({s} : Set S))) (x : X) (hx : f x = s) :
    FiniteType.QuasiFiniteAt f x := sorry

/-- For a locally finite type morphism, local quasi-finiteness is equivalent to discreteness of
every scheme-theoretic fiber and to discreteness after every base change from the spectrum of a
field. -/
theorem locallyQuasiFinite_tfae_discrete_fibers [LocallyOfFiniteType f] :
    List.TFAE
      [ LocallyQuasiFinite f
      , ∀ s : S, DiscreteTopology (f.fiber s)
      , ∀ (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ S),
          DiscreteTopology (pullback f g : Scheme)
      ] := sorry

/-- A scheme morphism is quasi-finite if and only if it is locally of finite type,
quasi-compact, and has finite point-set fibers over every target point. -/
theorem quasiFinite_iff_locallyOfFiniteType_and_quasiCompact_and_finiteFibers :
    QuasiFinite f ↔
      LocallyOfFiniteType f ∧ QuasiCompact f ∧
        ∀ s : S, Set.Finite ((fun x : X ↦ f x) ⁻¹' ({s} : Set S)) := sorry

/-- For a finite type morphism, the points in a fixed point-set fiber at which the morphism is
quasi-finite form a finite set. -/
theorem FiniteType.finiteQuasiFiniteAtPointsOver [FiniteType f] (s : S) :
    ({x : X | f x = s ∧ f.QuasiFiniteAt x} : Set X).Finite := sorry

end Scheme.Hom
end AlgebraicGeometry
