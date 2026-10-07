module

public import stacks_project.Chap64.Proposition_64_29_3_AmbientCohomology
public import stacks_project.Chap64.Lemma_64_29_1_GaloisModule
public import stacks_project.Chap59.Lemma_59_65_1_Equivalence

/-!
# Ambient geometric invariants and their residual degree-zero comparison

Derive invariants on all discrete continuous geometric representations, then
restrict the input to finite arithmetic representations. Residual degree-zero
actions use arithmetic lifts on invariant vectors and the canonical derived unit.
-/

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

/-- Restrict an arithmetic continuous representation to geometric π₁. -/
def restriction :
    DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar))) ⥤
      DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber ηbar)) :=
  discreteModuleRes (geometricToArithmetic X ηbar).hom

/-- Geometric invariants on all arithmetic continuous representations. -/
def invariants :
    DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar))) ⥤
      ModuleCat.{u + 1} Λ :=
  restriction Λ X ηbar ⋙
    AmbientDiscreteCohomology.invariants Λ (Aut (standardFiniteEtaleFiber ηbar))

/-- Continuous geometric cohomology, derived before imposing finite input. -/
def cohomology (i : ℕ) :
    DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar))) ⥤
      ModuleCat.{u + 1} Λ :=
  restriction Λ X ηbar ⋙
    AmbientDiscreteCohomology.cohomology Λ (Aut (standardFiniteEtaleFiber ηbar)) i

/-- The canonical degree-zero isomorphism is whiskering of the ambient derived unit. -/
def zeroIso : cohomology Λ X ηbar 0 ≅ invariants Λ X ηbar :=
  isoWhiskerLeft (restriction Λ X ηbar)
    (AmbientDiscreteCohomology.zeroIso Λ (Aut (standardFiniteEtaleFiber ηbar)))

/-- Finite inputs are included only after the ambient right derived functor exists. -/
def finiteCohomology (i : ℕ) :
    (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory ⥤
        ModuleCat.{u + 1} Λ :=
  (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).ι ⋙ cohomology Λ X ηbar i

/-- The inclusion of finite inputs preserves the specified degree-zero comparison. -/
def finiteZeroIso : finiteCohomology Λ X ηbar 0 ≅
    (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).ι ⋙ invariants Λ X ηbar :=
  isoWhiskerLeft _ (zeroIso Λ X ηbar)

variable (M : DiscreteModuleCat Λ
  (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar))))

/-- Normality of geometric π₁ makes arithmetic lifts preserve geometric invariants. -/
theorem arithmeticLift_mem_invariants (σ : Gal(AlgebraicClosure k/k))
    (m : (invariants Λ X ηbar).obj M) :
    (M.obj.ρ (arithmeticLift X ηbar σ)).hom m.val ∈
      (((Rep.ActionToRep Λ (Aut (standardFiniteEtaleFiber ηbar))).obj
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
    (a : Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))
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
      (AmbientDiscreteCohomology.degreeZeroUnit Λ
        (Aut (standardFiniteEtaleFiber ηbar))).app ((restriction Λ X ηbar).obj M) := rfl

/-- The degree-zero comparison commutes with the residual Galois action. -/
theorem residualZeroIso_equivariant (σ : Gal(AlgebraicClosure k/k)) :
    (residualCohomologyZero Λ X ηbar M).ρ σ ≫ (residualZeroIso Λ X ηbar M).hom.hom =
      (residualZeroIso Λ X ηbar M).hom.hom ≫ (residualInvariants Λ X ηbar M).ρ σ :=
  (residualZeroIso Λ X ηbar M).hom.comm σ

end AlgebraicGeometry.SchemeOverField.Ambient
