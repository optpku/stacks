module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricInvariants
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualGaloisModule

/-! Residual Galois actions on invariant vectors and their degree-zero cohomology comparison. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Action.ModuleCat
open CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.Ambient

variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))

variable (M : DiscreteModuleCat Λ
  (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar))))

/-- Normality of geometric π₁ makes arithmetic lifts preserve geometric invariants. -/
theorem arithmeticLift_mem_invariants (σ : Gal(AlgebraicClosure k/k))
    (m : (invariants Λ X ηbar).obj M) :
    (M.obj.ρ (arithmeticLift X ηbar σ)).hom m.val ∈
      (((Rep.ActionToRep Λ (Aut (GeometricPoint.finiteFiber ηbar))).obj
        ((restriction Λ X ηbar).obj M).obj).ρ).invariants := sorry

/-- The actual residual action sends an invariant vector to its arithmetic translate. -/
def residualEnd (σ : Gal(AlgebraicClosure k/k)) :
    (invariants Λ X ηbar).obj M ⟶ (invariants Λ X ηbar).obj M :=
  ModuleCat.ofHom
    { toFun := fun m ↦ ⟨(M.obj.ρ (arithmeticLift X ηbar σ)).hom m.val,
        arithmeticLift_mem_invariants Λ X ηbar M σ m⟩
      map_add' := fun m n ↦ Subtype.ext ((M.obj.ρ _).hom.map_add m.val n.val)
      map_smul' := fun a m ↦ Subtype.ext ((M.obj.ρ _).hom.map_smul a m.val) }

/-- On geometric invariants, the translate depends only on the residual Galois element. -/
theorem arithmeticLift_independent (σ : Gal(AlgebraicClosure k/k))
    (a : Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
    (ha : arithmeticToGalois X (arithmeticPoint X ηbar) a = galoisToGaloisPoint X ηbar σ)
    (m : (invariants Λ X ηbar).obj M) :
    (M.obj.ρ a).hom m.val = ((residualEnd Λ X ηbar M σ).hom m).val := sorry

/-- The identity residual element acts identically on invariant vectors. -/
theorem residualEnd_one : residualEnd Λ X ηbar M 1 = 𝟙 _ := sorry

/-- Residual multiplication follows arithmetic multiplication modulo geometric π₁. -/
theorem residualEnd_mul (σ τ : Gal(AlgebraicClosure k/k)) :
    residualEnd Λ X ηbar M (σ * τ) =
      residualEnd Λ X ηbar M τ ≫ residualEnd Λ X ηbar M σ := sorry

/-- Geometric invariants with the residual Galois action on their actual vectors. -/
def residualInvariants : Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) where
  V := (invariants Λ X ηbar).obj M
  ρ :=
    { toFun := residualEnd Λ X ηbar M
      map_one' := residualEnd_one Λ X ηbar M
      map_mul' := residualEnd_mul Λ X ηbar M }

/-- Residual action on ambient degree-zero cohomology transported by the canonical unit. -/
def residualCohomologyZero : Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) where
  V := (cohomology Λ X ηbar 0).obj M
  ρ := (((zeroIso Λ X ηbar).app M).symm.conj.toMonoidHom).comp
    (residualInvariants Λ X ηbar M).ρ

/-- The degree-zero canonical comparison is equivariant for the specified residual action. -/
def residualZeroIso : residualCohomologyZero Λ X ηbar M ≅ residualInvariants Λ X ηbar M :=
  Action.mkIso ((zeroIso Λ X ηbar).app M) fun σ ↦ by
    change (((zeroIso Λ X ηbar).app M).hom ≫
      residualEnd Λ X ηbar M σ ≫ ((zeroIso Λ X ηbar).app M).inv) ≫
        ((zeroIso Λ X ηbar).app M).hom =
      ((zeroIso Λ X ηbar).app M).hom ≫ residualEnd Λ X ηbar M σ
    rw [Category.assoc, Category.assoc, ((zeroIso Λ X ηbar).app M).inv_hom_id]
    simp

/-- The equivariant inverse is the ambient derived unit on the geometric restriction. -/
theorem residualZeroIso_inv :
    (residualZeroIso Λ X ηbar M).inv.hom =
      (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.toDerivedCohomologyZero Λ
        (Aut (GeometricPoint.finiteFiber ηbar))).app ((restriction Λ X ηbar).obj M) := rfl

/-- The degree-zero comparison commutes with the residual Galois action. -/
theorem residualZeroIso_equivariant (σ : Gal(AlgebraicClosure k/k)) :
    (residualCohomologyZero Λ X ηbar M).ρ σ ≫ (residualZeroIso Λ X ηbar M).hom.hom =
      (residualZeroIso Λ X ηbar M).hom.hom ≫ (residualInvariants Λ X ηbar M).ρ σ :=
  (residualZeroIso Λ X ηbar M).hom.comm σ

end AlgebraicGeometry.SchemeOverField.Ambient
