module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualHomology
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Finite discrete left coefficients for continuous residual homology

Keep the original module and group action, with their finite discrete topology.
The right-coefficient resolution is used at `R = Λᵐᵒᵖ`, so its input has left
`Λᵐᵒᵖᵐᵒᵖ` coefficients.  Restriction along the canonical double-opposite ring
equivalence changes only the spelling of scalars, never left into right action.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
noncomputable section
universe u

namespace FiniteCompactInput

variable {Λ Γ : Type u} [Ring Λ] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- The original finite module, equipped with the discrete compact Hausdorff topology. -/
def compactModule (V : ModuleCat.{u} Λ) [Finite V] : NoncommCompactModule Λ :=
  -- Local instance justification (defeq pin): This constructor equips the original finite module carrier with the specified discrete topology.
  letI : TopologicalSpace V := ⊥
  -- Local instance justification (defeq pin): The preceding topology is definitionally discrete, as required by this constructor's continuity fields.
  letI : DiscreteTopology V := ⟨rfl⟩
  { toModule := V
    scalarContinuous := ⟨fun _ ↦ continuous_of_discreteTopology⟩ }

/-- The original linear action, now continuous on the finite discrete carrier. -/
def compactAction (M : DiscreteModuleCat Λ Γ) [Finite M.obj.V] :
    Action (NoncommCompactModule Λ) Γ where
  V := compactModule M.obj.V
  ρ :=
    { toFun := fun γ ↦
        { toLinearMap := (M.obj.ρ γ).hom
          cont := by
            -- Local instance justification (defeq pin): compactModule fixes the discrete topology on this same carrier; this proof uses that exact instance.
            letI : DiscreteTopology (compactModule M.obj.V).toModule := ⟨rfl⟩
            exact continuous_of_discreteTopology }
      map_one' := by
        apply ContinuousLinearMap.ext
        intro x
        change (M.obj.ρ 1).hom x = x
        simp
      map_mul' := by
        intro γ δ
        apply ContinuousLinearMap.ext
        intro x
        change (M.obj.ρ (γ * δ)).hom x = (M.obj.ρ γ).hom ((M.obj.ρ δ).hom x)
        rw [map_mul]
        rfl }

/-- Open stabilizers give joint continuity of this specified discrete action. -/
theorem compactAction_continuous (M : DiscreteModuleCat Λ Γ) [Finite M.obj.V] :
    NoncommCompactRepresentation.continuousAction Λ Γ (compactAction M) := by
  -- Local instance justification (defeq pin): The continuity theorem concerns the same discrete topology used by compactModule.
  letI : TopologicalSpace M.obj.V := ⊥
  -- Local instance justification (defeq pin): This discreteness witness belongs to the topology fixed immediately above.
  letI : DiscreteTopology M.obj.V := ⟨rfl⟩
  -- Local instance justification (proof-local temporary data): The given open stabilizers prove continuity of this exact group action on its discrete carrier.
  letI : ContinuousSMul Γ M.obj.V := (OpenStabilizer.continuousSMul_iff Λ Γ M.obj).mpr M.property
  exact (continuous_smul : Continuous (fun gm : Γ × M.obj.V ↦ gm.1 • gm.2))

/-- Compact representation with the same vectors, left scalars, and group maps. -/
def ofFinite (M : DiscreteModuleCat Λ Γ) [Finite M.obj.V] :
    NoncommCompactRepresentation.Cat Λ Γ :=
  ⟨compactAction M, compactAction_continuous M⟩

/-- Finitely generated coefficients over a finite ring are finite as a set. -/
def ofFiniteModule [Finite Λ] (M : DiscreteModuleCat Λ Γ) [Module.Finite Λ M.obj.V] :
    NoncommCompactRepresentation.Cat Λ Γ :=
  -- Local instance justification (proof-local temporary data): Finite generation over the finite coefficient ring makes this input module finite.
  letI : Finite M.obj.V := Module.finite_of_finite Λ
  ofFinite M

@[simp] theorem ofFinite_action (M : DiscreteModuleCat Λ Γ) [Finite M.obj.V]
    (γ : Γ) (m : M.obj.V) :
    (show _ →L[Λ] _ from (ofFinite M).obj.ρ γ) m = (M.obj.ρ γ).hom m := rfl

/-- Forgetting the compact topology recovers precisely the original module. -/
def forgetIso (M : DiscreteModuleCat Λ Γ) [Finite M.obj.V] :
    (NoncommCompactModule.forget Λ).obj (ofFinite M).obj.V ≅ M.obj.V := Iso.refl _

@[simp] theorem forgetIso_hom_apply (M : DiscreteModuleCat Λ Γ) [Finite M.obj.V]
    (m : M.obj.V) : (forgetIso M).hom m = m := rfl

/-- The original maps between coefficients remain continuous and equivariant. -/
def map {M N : DiscreteModuleCat Λ Γ} [Finite M.obj.V] [Finite N.obj.V] (f : M ⟶ N) :
    ofFinite M ⟶ ofFinite N :=
  ObjectProperty.homMk
    { hom :=
        { toLinearMap := f.hom.hom.hom
          cont := by
            -- Local instance justification (defeq pin): ofFinite retains the exact discrete carrier topology needed to prove continuity of the original linear map.
            letI : DiscreteTopology (ofFinite M).obj.V.toModule := ⟨rfl⟩
            exact continuous_of_discreteTopology }
      comm γ := by
        apply ContinuousLinearMap.ext
        intro x
        exact congrArg (fun h ↦ h.hom x) (f.hom.comm γ) }

@[simp] theorem map_apply {M N : DiscreteModuleCat Λ Γ} [Finite M.obj.V] [Finite N.obj.V]
    (f : M ⟶ N) (m : M.obj.V) : (show _ →L[Λ] _ from (map f).hom.hom) m = f.hom.hom m := rfl

/-- Restrict along `(opOp Λ).symm`, so double-op scalars act by the original left action. -/
def doubleOpDiscrete (M : DiscreteModuleCat Λ Γ) : DiscreteModuleCat Λᵐᵒᵖᵐᵒᵖ Γ :=
  ⟨((ModuleCat.restrictScalars (RingEquiv.opOp Λ).symm.toRingHom).mapAction Γ).obj M.obj,
    by
      intro m
      exact M.property m⟩

/-- The explicit input expected by residual homology at `R = Λᵐᵒᵖ`. -/
def residualInput [Finite Λ] (M : DiscreteModuleCat Λ Γ) [Module.Finite Λ M.obj.V] :
    NoncommCompactRepresentation.Cat Λᵐᵒᵖᵐᵒᵖ Γ :=
  -- Local instance justification (proof-local temporary data): Finite generation over the finite coefficient ring makes this input module finite.
  letI : Finite M.obj.V := Module.finite_of_finite Λ
  -- Local instance justification (defeq pin): Double-opposite scalar restriction leaves the carrier unchanged, so reuse its finiteness witness.
  letI : Finite (doubleOpDiscrete M).obj.V := inferInstanceAs (Finite M.obj.V)
  ofFinite (doubleOpDiscrete M)

@[simp] theorem residualInput_action [Finite Λ] (M : DiscreteModuleCat Λ Γ)
    [Module.Finite Λ M.obj.V] (γ : Γ) (m : M.obj.V) :
    (show _ →L[Λᵐᵒᵖᵐᵒᵖ] _ from (residualInput M).obj.ρ γ) m = (M.obj.ρ γ).hom m := rfl

@[simp] theorem residualInput_smul [Finite Λ] (M : DiscreteModuleCat Λ Γ)
    [Module.Finite Λ M.obj.V] (a : Λ) (m : M.obj.V) :
    (RingEquiv.opOp Λ a) • (show (residualInput M).obj.V.toModule from m) = a • m := rfl

/-- Identity on vectors after restricting double-op coefficients back to Λ. -/
def residualInputForgetIso [Finite Λ] (M : DiscreteModuleCat Λ Γ) [Module.Finite Λ M.obj.V] :
    (ModuleCat.restrictScalars (RingEquiv.opOp Λ).toRingHom).obj
      (residualInput M).obj.V.toModule ≅ M.obj.V :=
  (LinearEquiv.refl Λ M.obj.V).toModuleIso

@[simp] theorem residualInputForgetIso_hom_apply [Finite Λ] (M : DiscreteModuleCat Λ Γ)
    [Module.Finite Λ M.obj.V] (m : M.obj.V) : (residualInputForgetIso M).hom m = m := rfl

end FiniteCompactInput
