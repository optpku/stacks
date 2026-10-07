module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.ClosedSubscheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.HilbertClosedSubscheme

/-!
# Cycle classes of Hilbert generators

This file sends a closed subscheme of bounded relative dimension to its
associated family of cycles on fibres and extends that assignment linearly.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- A relative-dimension bound on `Z ⟶ S` implies the fibrewise Krull-dimension
bound used by the associated-cycle construction. -/
theorem fiberClosedSubschemeDimensionLE_of_relativeDimensionLE
    (f : X ⟶ S) (Z : X.IdealSheafData) (r : ℕ)
    (h : RelativeDimensionLE (Z.subschemeι ≫ f) r) :
    f.fiberClosedSubschemeDimensionLE Z r := sorry

/-- The family of `r`-cycles on fibres associated to a generator of
`Hilb(X/S, r)`. -/
noncomputable def hilbertCycleClassValue (f : X ⟶ S) [LocallyOfFiniteType f]
    (r : ℕ) (Z : f.HilbertClosedSubscheme r) : f.FiberCycleFamily (r : ℤ) :=
  let dimensionBound : f.fiberClosedSubschemeDimensionLE Z.ideal r := by
    have fiber_asFiber_heq : ∀ {Y T : Scheme.{u}} (g : Y ⟶ T) {x : Y} {s : T}
        (q : g.fiber s) (h_point : g x = s) (h_fiber : g.fiberι s q = x),
        HEq (g.asFiber x) q := by
      intro Y T g x s q h_point h_fiber
      have h_q : g.asFiber x =
          @Eq.ndrec T s (fun t => (g.fiber t : Type _)) q (g x) h_point.symm := by
        cases h_point
        apply (g.fiberι (g x)).isEmbedding.injective
        rw [g.fiberι_asFiber]
        exact h_fiber.symm
      have h_cast : HEq
          (@Eq.ndrec T s (fun t => (g.fiber t : Type _)) q (g x) h_point.symm) q := by
        exact @eqRec_heq T (fun t => (g.fiber t : Type _)) s (g x) h_point.symm q
      exact h_q ▸ h_cast
    intro s
    let g : Z.ideal.subscheme ⟶ S := Z.ideal.subschemeι ≫ f
    let e : (f.fiberClosedSubscheme Z.ideal s).subscheme ≃ₜ g.fiber s :=
      Scheme.homeoOfIso (fiberClosedSubschemeIso f Z.ideal s)
    rw [e.isHomeomorph.topologicalKrullDim_eq]
    rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt]
    apply iSup_le
    intro q
    let x : Z.ideal.subscheme := g.fiberι s q
    have h_point : g x = s := by
      have h_mem : x ∈ g ⁻¹' ({s} : Set S) := by
        rw [← g.range_fiberι s]
        exact ⟨q, rfl⟩
      exact h_mem
    have h_dimension := Z.relativeDimensionLE.relativeDimensionLEAt x
    change g.fiberDimensionAt x ≤ (r : WithBot ℕ∞) at h_dimension
    have h_local : topologicalKrullDimAt (g.asFiber x) ≤ (r : WithBot ℕ∞) := by
      rw [← fiberDimensionAt_eq_topologicalKrullDimAt_asFiber g x]
      exact h_dimension
    have h_q : HEq (g.asFiber x) q := fiber_asFiber_heq g q h_point rfl
    have h_sigma : (⟨g x, g.asFiber x⟩ : Σ t : S, g.fiber t) = ⟨s, q⟩ :=
      Sigma.ext h_point h_q
    have h_prop := congrArg (fun z : Σ t : S, g.fiber t =>
      topologicalKrullDimAt z.2 ≤ (r : WithBot ℕ∞)) h_sigma
    exact h_prop ▸ h_local
  closedSubschemeFiberCycleFamily f Z.ideal r dimensionBound

/-- The generator evaluation agrees with the associated fibrewise cycle family
of the underlying closed subscheme. -/
theorem hilbertCycleClassValue_eq_closedSubschemeFiberCycleFamily
    (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (Z : f.HilbertClosedSubscheme r) :
    hilbertCycleClassValue f r Z =
      closedSubschemeFiberCycleFamily f Z.ideal r
        (fiberClosedSubschemeDimensionLE_of_relativeDimensionLE f Z.ideal r
          Z.relativeDimensionLE) := sorry

/-- The homomorphism sending a finite formal sum of Hilbert generators to the
corresponding family of `r`-cycles on fibres of `X/S`. -/
noncomputable def hilbertCycleClass (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ) :
    FreeAbelianGroup (f.HilbertClosedSubscheme r) →+ f.FiberCycleFamily (r : ℤ) :=
  FreeAbelianGroup.lift (hilbertCycleClassValue f r)

/-- A generator `[Z]` is sent to the associated family `[Z/X/S]ᵣ`. -/
theorem hilbertCycleClass_of (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (Z : f.HilbertClosedSubscheme r) :
    hilbertCycleClass f r (FreeAbelianGroup.of Z) =
      hilbertCycleClassValue f r Z := sorry

end AlgebraicGeometry.Scheme.Hom
