/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.GradedSections
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Functorial
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Map

/-!
# Canonical graded action on twisted cohomology

The homogeneous action of a graded ring on truncated global sections of tensor twists is
specified by the associated-sheaf morphisms induced by multiplication.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Proj

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (F : (Proj 𝒜).Modules) (k : ℤ)

/-- An action of the graded ring on truncated global sections is canonical when multiplication
by every homogeneous element agrees with the cohomology map induced by multiplication between
the corresponding associated twisting sheaves. -/
def IsCanonicalTruncatedTwistCohomologyAction
    (moduleAction : Module A
      (truncatedTwistGlobalSections 𝒜
        (ProjTwistFamily.tensorTwist (AssociatedModule.twistingSheaf 𝒜) F) k)) : Prop :=
  -- Expose only the supplied action locally for `•`; no canonical instance is registered.
  letI : Module A
      (truncatedTwistGlobalSections 𝒜
        (ProjTwistFamily.tensorTwist (AssociatedModule.twistingSheaf 𝒜) F) k) := moduleAction
  ∀ {m : ℕ} (p : 𝒜 m) (d : {d : ℤ // k ≤ d})
    (x : (RingedSpace.moduleCohomology
      (ProjTwistFamily.tensorTwist (AssociatedModule.twistingSheaf 𝒜) F d.1) 0 : Type u)),
    let twistMap : AssociatedModule.twistingSheaf 𝒜 d.1 ⟶
        AssociatedModule.twistingSheaf 𝒜 (d.1 + (m : ℤ)) :=
      @AssociatedModule.map
        ℤ A A A
        _ _ _ _ _ _ _ _ _
        (Submodule ℤ A) _ _
        𝒜 _
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading 𝒜) d.1)
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading 𝒜) (d.1 + (m : ℤ)))
        (GradedModule.shiftDecomposition
          (DirectSum.Decomposition.natToIntGrading 𝒜) d.1)
        (GradedModule.shiftDecomposition
          (DirectSum.Decomposition.natToIntGrading 𝒜) (d.1 + (m : ℤ)))
        inferInstance inferInstance
        (LinearMap.mulLeft A p.1)
        (fun i g hg ↦ by
          have hg' : g ∈ GradedModule.shiftGrading
              (DirectSum.Decomposition.natToIntGrading 𝒜) d.1 i := hg
          apply (GradedModule.mem_shiftGrading_iff
            (DirectSum.Decomposition.natToIntGrading 𝒜)
            (d.1 + (m : ℤ)) i).mpr
          rw [GradedModule.mem_shiftGrading_iff] at hg'
          change p.1 * g ∈
            (DirectSum.Decomposition.natToIntGrading 𝒜)
              (i + (d.1 + (m : ℤ)))
          simpa [smul_eq_mul, add_assoc, add_comm, add_left_comm] using
            SetLike.GradedSMul.smul_mem p.2 hg')
    (p : A) • DirectSum.of
        (fun e : {e : ℤ // k ≤ e} ↦
          (RingedSpace.moduleCohomology
            (ProjTwistFamily.tensorTwist (AssociatedModule.twistingSheaf 𝒜) F e.1) 0 :
              Type u)) d x =
      DirectSum.of
        (fun e : {e : ℤ // k ≤ e} ↦
          (RingedSpace.moduleCohomology
            (ProjTwistFamily.tensorTwist (AssociatedModule.twistingSheaf 𝒜) F e.1) 0 :
              Type u))
        ⟨d.1 + (m : ℤ), by omega⟩
        ((RingedSpace.moduleCohomologyMap (𝟙 F ⊗ₘ twistMap) 0).hom x)

namespace IsCanonicalTruncatedTwistCohomologyAction

/-- Multiplication by a homogeneous element in a canonical action is the cohomology map induced
by the corresponding multiplication morphism between associated twisting sheaves. -/
theorem smul_of
    (moduleAction : Module A
      (truncatedTwistGlobalSections 𝒜
        (ProjTwistFamily.tensorTwist (AssociatedModule.twistingSheaf 𝒜) F) k))
    (h : IsCanonicalTruncatedTwistCohomologyAction 𝒜 F k moduleAction)
    {m : ℕ} (p : 𝒜 m) (d : {d : ℤ // k ≤ d})
    (x : (RingedSpace.moduleCohomology
      (ProjTwistFamily.tensorTwist (AssociatedModule.twistingSheaf 𝒜) F d.1) 0 : Type u)) :
    -- Expose only the supplied action locally for `•`; no canonical instance is registered.
    letI : Module A
        (truncatedTwistGlobalSections 𝒜
          (ProjTwistFamily.tensorTwist (AssociatedModule.twistingSheaf 𝒜) F) k) := moduleAction
    let twistMap : AssociatedModule.twistingSheaf 𝒜 d.1 ⟶
        AssociatedModule.twistingSheaf 𝒜 (d.1 + (m : ℤ)) :=
      @AssociatedModule.map
        ℤ A A A
        _ _ _ _ _ _ _ _ _
        (Submodule ℤ A) _ _
        𝒜 _
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading 𝒜) d.1)
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading 𝒜) (d.1 + (m : ℤ)))
        (GradedModule.shiftDecomposition
          (DirectSum.Decomposition.natToIntGrading 𝒜) d.1)
        (GradedModule.shiftDecomposition
          (DirectSum.Decomposition.natToIntGrading 𝒜) (d.1 + (m : ℤ)))
        inferInstance inferInstance
        (LinearMap.mulLeft A p.1)
        (fun i g hg ↦ by
          have hg' : g ∈ GradedModule.shiftGrading
              (DirectSum.Decomposition.natToIntGrading 𝒜) d.1 i := hg
          apply (GradedModule.mem_shiftGrading_iff
            (DirectSum.Decomposition.natToIntGrading 𝒜)
            (d.1 + (m : ℤ)) i).mpr
          rw [GradedModule.mem_shiftGrading_iff] at hg'
          change p.1 * g ∈
            (DirectSum.Decomposition.natToIntGrading 𝒜)
              (i + (d.1 + (m : ℤ)))
          simpa [smul_eq_mul, add_assoc, add_comm, add_left_comm] using
            SetLike.GradedSMul.smul_mem p.2 hg')
    (p : A) • DirectSum.of
        (fun e : {e : ℤ // k ≤ e} ↦
          (RingedSpace.moduleCohomology
            (ProjTwistFamily.tensorTwist (AssociatedModule.twistingSheaf 𝒜) F e.1) 0 :
              Type u)) d x =
      DirectSum.of
        (fun e : {e : ℤ // k ≤ e} ↦
          (RingedSpace.moduleCohomology
            (ProjTwistFamily.tensorTwist (AssociatedModule.twistingSheaf 𝒜) F e.1) 0 :
              Type u))
        ⟨d.1 + (m : ℤ), by omega⟩
        ((RingedSpace.moduleCohomologyMap (𝟙 F ⊗ₘ twistMap) 0).hom x) :=
  h p d x

end IsCanonicalTruncatedTwistCohomologyAction

end AlgebraicGeometry.Proj
