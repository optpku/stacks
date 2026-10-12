/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.RestrictScalars
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Determinant.TwoTerm.RestrictScalars
public import ReasLib.Algebra.Category.ModuleCat.ShortComplex

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Module.Determinant TensorProduct

noncomputable section

universe u

namespace CategoryTheory.ShortComplex.ShortExact.ExteriorComparison

variable {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
variable {S₁ : ShortComplex (ModuleCat.{u} R₁)}
variable {S₂ : ShortComplex (ModuleCat.{u} R₂)}
variable {N₁ : ModuleCat.{u} R₁} {N₂ : ModuleCat.{u} R₂}

/-- The middle vertical map followed by the second cokernel projection kills the first
differential. -/
theorem cokernelMap_condition (φ : R₁ →+* R₂)
    (F : S₁ ⟶ S₂.map (ModuleCat.restrictScalars φ))
    (dL₁ : N₁ ⟶ S₁.X₂) (dL₂ : N₂ ⟶ S₂.X₂)
    (fN : N₁ ⟶ (ModuleCat.restrictScalars φ).obj N₂)
    (hL : dL₁ ≫ F.τ₂ = fN ≫ (ModuleCat.restrictScalars φ).map dL₂) :
    dL₁ ≫ F.τ₂ ≫ (ModuleCat.restrictScalars φ).map (cokernel.π dL₂) = 0 := sorry

/-- The map on the cokernel models scalar change on `H⁰` of the two-term complex. -/
noncomputable def cokernelMap (φ : R₁ →+* R₂)
    (F : S₁ ⟶ S₂.map (ModuleCat.restrictScalars φ))
    (dL₁ : N₁ ⟶ S₁.X₂) (dL₂ : N₂ ⟶ S₂.X₂)
    (fN : N₁ ⟶ (ModuleCat.restrictScalars φ).obj N₂)
    (hL : dL₁ ≫ F.τ₂ = fN ≫ (ModuleCat.restrictScalars φ).map dL₂) :
    cokernel dL₁ ⟶ (ModuleCat.restrictScalars φ).obj (cokernel dL₂) :=
  cokernel.desc dL₁
    (F.τ₂ ≫ (ModuleCat.restrictScalars φ).map (cokernel.π dL₂))
    (cokernelMap_condition φ F dL₁ dL₂ fN hL)

/-- The induced cokernel map is characterized after the first cokernel projection. -/
theorem cokernelMap_π (φ : R₁ →+* R₂)
    (F : S₁ ⟶ S₂.map (ModuleCat.restrictScalars φ))
    (dL₁ : N₁ ⟶ S₁.X₂) (dL₂ : N₂ ⟶ S₂.X₂)
    (fN : N₁ ⟶ (ModuleCat.restrictScalars φ).obj N₂)
    (hL : dL₁ ≫ F.τ₂ = fN ≫ (ModuleCat.restrictScalars φ).map dL₂) :
    cokernel.π dL₁ ≫ cokernelMap φ F dL₁ dL₂ fN hL =
      F.τ₂ ≫ (ModuleCat.restrictScalars φ).map (cokernel.π dL₂) := sorry

/-- The semilinear tensor-product function obtained by applying two scalar-change morphisms. -/
noncomputable def tensorMapFun (φ : R₁ →+* R₂)
    {A₁ B₁ : ModuleCat.{u} R₁} {A₂ B₂ : ModuleCat.{u} R₂}
    (fA : A₁ ⟶ (ModuleCat.restrictScalars φ).obj A₂)
    (fB : B₁ ⟶ (ModuleCat.restrictScalars φ).obj B₂) :
    A₁ ⊗[R₁] B₁ →ₛₗ[φ] A₂ ⊗[R₂] B₂ :=
  TensorProduct.map
    ((ModuleCat.semilinearMapAddEquiv φ A₁ A₂).symm fA)
    ((ModuleCat.semilinearMapAddEquiv φ B₁ B₂).symm fB)

/-- The semilinear tensor-product function applies the two maps on pure tensors. -/
theorem tensorMapFun_tmul (φ : R₁ →+* R₂)
    {A₁ B₁ : ModuleCat.{u} R₁} {A₂ B₂ : ModuleCat.{u} R₂}
    (fA : A₁ ⟶ (ModuleCat.restrictScalars φ).obj A₂)
    (fB : B₁ ⟶ (ModuleCat.restrictScalars φ).obj B₂)
    (x : A₁) (y : B₁) :
    tensorMapFun φ fA fB (x ⊗ₜ[R₁] y) =
      (ModuleCat.semilinearMapAddEquiv φ A₁ A₂).symm fA x ⊗ₜ[R₂]
        (ModuleCat.semilinearMapAddEquiv φ B₁ B₂).symm fB y := sorry

/-- The categorical tensor-product map obtained by applying two scalar-change morphisms. -/
noncomputable def tensorMap (φ : R₁ →+* R₂)
    {A₁ B₁ : ModuleCat.{u} R₁} {A₂ B₂ : ModuleCat.{u} R₂}
    (fA : A₁ ⟶ (ModuleCat.restrictScalars φ).obj A₂)
    (fB : B₁ ⟶ (ModuleCat.restrictScalars φ).obj B₂) :
    ModuleCat.of R₁ (A₁ ⊗[R₁] B₁) ⟶
      (ModuleCat.restrictScalars φ).obj (ModuleCat.of R₂ (A₂ ⊗[R₂] B₂)) :=
  ModuleCat.semilinearMapAddEquiv φ
    (ModuleCat.of R₁ (A₁ ⊗[R₁] B₁)) (ModuleCat.of R₂ (A₂ ⊗[R₂] B₂))
    (tensorMapFun φ fA fB)

/-- The right vertical map in exterior-comparison naturality, combining exterior-power and
two-term determinant scalar change. -/
noncomputable def targetMap (φ : R₁ →+* R₂)
    (F : S₁ ⟶ S₂.map (ModuleCat.restrictScalars φ))
    (fN : N₁ ⟶ (ModuleCat.restrictScalars φ).obj N₂)
    [Module.Free R₁ N₁] [Module.Finite R₁ N₁]
    [Module.Free R₂ N₂] [Module.Finite R₂ N₂]
    [Module.Free R₁ S₁.X₃] [Module.Finite R₁ S₁.X₃]
    [Module.Free R₂ S₂.X₃] [Module.Finite R₂ S₂.X₃]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fN)]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ F.τ₃)]
    (p : ℕ) :
    ModuleCat.of R₁ (S₁.X₁.exteriorPower p ⊗[R₁]
      (det[R₁](N₁) →ₗ[R₁] det[R₁](S₁.X₃))) ⟶
      (ModuleCat.restrictScalars φ).obj
        (ModuleCat.of R₂ (S₂.X₁.exteriorPower p ⊗[R₂]
          (det[R₂](N₂) →ₗ[R₂] det[R₂](S₂.X₃)))) :=
  tensorMap φ (ModuleCat.exteriorPower.mapRestrictScalars φ F.τ₁ p)
    (ModuleCat.TwoTermDeterminant.mapRestrictScalars φ fN F.τ₃)

/-- The target map applies the exterior-power and two-term determinant maps on pure tensors. -/
theorem targetMap_tmul (φ : R₁ →+* R₂)
    (F : S₁ ⟶ S₂.map (ModuleCat.restrictScalars φ))
    (fN : N₁ ⟶ (ModuleCat.restrictScalars φ).obj N₂)
    [Module.Free R₁ N₁] [Module.Finite R₁ N₁]
    [Module.Free R₂ N₂] [Module.Finite R₂ N₂]
    [Module.Free R₁ S₁.X₃] [Module.Finite R₁ S₁.X₃]
    [Module.Free R₂ S₂.X₃] [Module.Finite R₂ S₂.X₃]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fN)]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ F.τ₃)]
    (p : ℕ) (x : S₁.X₁.exteriorPower p)
    (a : det[R₁](N₁) →ₗ[R₁] det[R₁](S₁.X₃)) :
    tensorMapFun φ (ModuleCat.exteriorPower.mapRestrictScalars φ F.τ₁ p)
        (ModuleCat.TwoTermDeterminant.mapRestrictScalars φ fN F.τ₃) (x ⊗ₜ[R₁] a) =
      (ModuleCat.semilinearMapAddEquiv φ (S₁.X₁.exteriorPower p)
          (S₂.X₁.exteriorPower p)).symm
          (ModuleCat.exteriorPower.mapRestrictScalars φ F.τ₁ p) x ⊗ₜ[R₂]
        (ModuleCat.semilinearMapAddEquiv φ
          (ModuleCat.of R₁ (det[R₁](N₁) →ₗ[R₁] det[R₁](S₁.X₃)))
          (ModuleCat.of R₂ (det[R₂](N₂) →ₗ[R₂] det[R₂](S₂.X₃)))).symm
          (ModuleCat.TwoTermDeterminant.mapRestrictScalars φ fN F.τ₃) a := sorry

/-- Exterior comparison is natural under a compatible change of scalars whose two maps in the
right-hand two-term complex become isomorphisms after scalar extension. Rings and module carriers
are taken in one fixed universe, matching the source's small-universe convention. -/
theorem naturality (φ : R₁ →+* R₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (F : S₁ ⟶ S₂.map (ModuleCat.restrictScalars.{u} φ))
    (fN : N₁ ⟶ (ModuleCat.restrictScalars.{u} φ).obj N₂)
    (dL₁ : N₁ ⟶ S₁.X₂) (dM₁ : N₁ ⟶ S₁.X₃)
    (dL₂ : N₂ ⟶ S₂.X₂) (dM₂ : N₂ ⟶ S₂.X₃)
    (hcomm₁ : dL₁ ≫ S₁.g = dM₁) (hcomm₂ : dL₂ ≫ S₂.g = dM₂)
    (hL : dL₁ ≫ F.τ₂ = fN ≫ (ModuleCat.restrictScalars.{u} φ).map dL₂)
    (hM : dM₁ ≫ F.τ₃ = fN ≫ (ModuleCat.restrictScalars.{u} φ).map dM₂)
    [Module.Free R₁ N₁] [Module.Finite R₁ N₁]
    [Module.Free R₂ N₂] [Module.Finite R₂ N₂]
    [Module.Free R₁ S₁.X₃] [Module.Finite R₁ S₁.X₃]
    [Module.Free R₂ S₂.X₃] [Module.Finite R₂ S₂.X₃]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fN)]
    [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ F.τ₃)]
    (hRank₁ : Module.finrank R₁ N₁ = Module.finrank R₁ S₁.X₃)
    (hRank₂ : Module.finrank R₂ N₂ = Module.finrank R₂ S₂.X₃)
    (p : ℕ) :
    ModuleCat.ofHom
        (CategoryTheory.ShortComplex.ShortExact.exteriorComparison hS₁ dL₁ dM₁
          hcomm₁ hRank₁ p) ≫ targetMap φ F fN p =
      ModuleCat.exteriorPower.mapRestrictScalars φ
          (cokernelMap φ F dL₁ dL₂ fN hL) p ≫
        (ModuleCat.restrictScalars.{u} φ).map
          (ModuleCat.ofHom
            (CategoryTheory.ShortComplex.ShortExact.exteriorComparison hS₂ dL₂ dM₂
              hcomm₂ hRank₂ p)) := sorry

end CategoryTheory.ShortComplex.ShortExact.ExteriorComparison

end
