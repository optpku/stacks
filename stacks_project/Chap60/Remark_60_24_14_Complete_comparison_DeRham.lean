/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Remark_60_24_9_Base_change_isomorphism_BaseSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineDifferentials
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineSheafExtension
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineTensorSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_ModuleDerivedSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_SheafDegreeBridges
public import stacks_project.Chap60.Remark_60_6_8_Connection
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_PDDeRham
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.LinearAlgebra.ExteriorPower.FormWedge
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients CrystallineSmoothLiftTerms
open scoped TensorProduct

universe u

namespace CrystallineCompleteConnection

section SheafDeRham

variable {A : Type u} [CommRing A]
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
variable (M : Y.Modules)
variable (nabla : asBaseSheaf f M ⟶ asBaseSheaf f (oneFormTensor f M))

/-- The degree-zero sheaf differential is the given connection, transported
through the canonical exterior-degree identifications. -/
noncomputable def sheafDifferential_zero :
    baseTerm f M 0 ⟶ baseTerm f M 1 :=
  (CrystallineSheafDegreeBridges.baseDegreeZero f M).hom ≫
    nabla ≫ (CrystallineSheafDegreeBridges.baseDegreeOne f M).inv

variable (U : Y.affineOpens)

/-- The sheaf of relative one-forms is quasi-coherent on a smooth morphism. -/
theorem oneForms_isQuasicoherent [Smooth f] : (oneForms f).IsQuasicoherent :=
  sorry

/-- Exterior powers of relative one-forms remain quasi-coherent. -/
theorem forms_isQuasicoherent [Smooth f] (n : ℕ) : (forms f n).IsQuasicoherent :=
  sorry

/-- Coherent coefficients are quasi-coherent. -/
theorem isQuasicoherent_of_isCoherent [M.IsCoherent] : M.IsQuasicoherent :=
  sorry

/-- Algebraic tensors with exterior forms compare with sheaf de Rham terms. -/
theorem affineTermCompare_bijective [Smooth f] [M.IsCoherent] (n : ℕ) :
    Function.Bijective
      ((CrystallineAffineTensorSections.tensorMap U M (forms f n)).comp
        (TensorProduct.map
          (LinearMap.id : Γ(M, U.1) →ₗ[Γ(Y, U.1)] Γ(M, U.1))
          (CrystallineAffineTensorSections.exteriorMap U (oneForms f) n))) :=
  sorry

/-- The canonical additive identification of algebraic tensors with sheaf
de Rham terms on an affine open. -/
noncomputable def affineTermEquiv [Smooth f] [M.IsCoherent] (n : ℕ) :
    Γ(M, U.1) ⊗[Γ(Y, U.1)]
        exteriorPower.form Γ(Y, U.1) Γ(oneForms f, U.1) n ≃+
      Γ(term f M n, U.1) :=
  AddEquiv.ofBijective
    ((CrystallineAffineTensorSections.tensorMap U M (forms f n)).comp
      (TensorProduct.map
        (LinearMap.id : Γ(M, U.1) →ₗ[Γ(Y, U.1)] Γ(M, U.1))
        (CrystallineAffineTensorSections.exteriorMap U (oneForms f) n)))
    (affineTermCompare_bijective f M U n)

/-- Affine identification of `asBaseSheaf` sections with module sections. -/
noncomputable def asBaseSectionsAddEquiv :
    ((asBaseSheaf f M).obj.obj (op U.1) : Type u) ≃+ Γ(M, U.1) :=
  AddEquiv.refl _

/-- Affine identification of sheaf de Rham term sections with module sections. -/
noncomputable def baseTermSectionsAddEquiv (n : ℕ) :
    ((baseTerm f M n).obj.obj (op U.1) : Type u) ≃+ Γ(term f M n, U.1) :=
  AddEquiv.refl _

/-- The given sheaf connection as an additive map of affine sections. -/
noncomputable def affineNablaHom :
    Γ(M, U.1) →+ Γ(oneFormTensor f M, U.1) :=
  (asBaseSectionsAddEquiv f (oneFormTensor f M) U).toAddMonoidHom.comp
    ((nabla.hom.app (op U.1)).hom.toAddMonoidHom.comp
      (asBaseSectionsAddEquiv f M U).symm.toAddMonoidHom)

/-- Algebraic tensors with one-forms compare with `M ⊗ Ω_{Y/S}` sections. -/
theorem tensorOneForm_bijective [Smooth f] [M.IsCoherent] :
    Function.Bijective (CrystallineAffineTensorSections.tensorMap U M (oneForms f)) :=
  sorry

/-- The canonical identification `Γ(M) ⊗ Γ(Ω) ≃ Γ(M ⊗ Ω)` on an affine open. -/
noncomputable def tensorOneFormEquiv [Smooth f] [M.IsCoherent] :
    Γ(M, U.1) ⊗[Γ(Y, U.1)] Γ(oneForms f, U.1) ≃+ Γ(oneFormTensor f M, U.1) :=
  AddEquiv.ofBijective (CrystallineAffineTensorSections.tensorMap U M (oneForms f))
    (tensorOneForm_bijective f M U)

/-- A sheaf connection must satisfy the actual affine Leibniz identity.
A-linearity alone is insufficient: even the zero map generally fails this law. -/
class IsConnection : Prop where
  /-- The scalar derivative term is the actual sheaf tensor of m and db. -/
  leibniz (V : Y.affineOpens) (b : Γ(Y, V.1)) (m : Γ(M, V.1)) :
    affineNablaHom f M nabla V (b • m) -
      b • affineNablaHom f M nabla V m =
        (SheafOfModules.RingedSite.tensorSection Y.sheaf (op V.1) m
          (CrystallineAffineDifferentials.sectionDerivation f V b) : Γ(oneFormTensor f M, V.1))

/-- The affine connection map `M → M ⊗ Ω` associated with the sheaf connection. -/
noncomputable def affineConnectionHom [Smooth f] [M.IsCoherent] :
    Γ(M, U.1) →+ Γ(M, U.1) ⊗[Γ(Y, U.1)] Γ(oneForms f, U.1) :=
  (tensorOneFormEquiv f M U).symm.toAddMonoidHom.comp (affineNablaHom f M nabla U)

variable [hConn : IsConnection f M nabla]

include hConn in
/-- The specified affine tensor comparison transfers the sheaf Leibniz law.
The hypothesis is retained; this is not asserted for arbitrary A-linear maps. -/
theorem affineConnection_leibniz [Smooth f] [M.IsCoherent]
    (b : Γ(Y, U.1)) (m : Γ(M, U.1)) :
    affineConnectionHom f M nabla U (b • m) =
      b • affineConnectionHom f M nabla U m +
        m ⊗ₜ[Γ(Y, U.1)] CrystallineAffineDifferentials.sectionDerivation f U b := sorry

/-- The affine connection packaged from the given sheaf morphism. -/
noncomputable def affineConnection [Smooth f] [M.IsCoherent] :=
  -- Local instance justification (noncanonical choice): the structure map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) :=
    (CrystallineAffineDifferentials.baseMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(oneForms f, U.1) :=
    Module.compHom _ (CrystallineAffineDifferentials.baseMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(oneForms f, U.1)
  (Connection.of (affineConnectionHom f M nabla U) (affineConnection_leibniz f M nabla U) :
    Connection (CrystallineAffineDifferentials.derivation f U) Γ(M, U.1))

/-- The affine exterior-form differential family, transported from the
algebraic de Rham family along the canonical Kähler comparison. -/
noncomputable def affineFamily :=
  -- Local instance justification (noncanonical choice): the structure map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) :=
    (CrystallineAffineDifferentials.baseMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(oneForms f, U.1) :=
    Module.compHom _ (CrystallineAffineDifferentials.baseMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(oneForms f, U.1)
  fun k ↦
    (exteriorPower.form.mapRestrictScalars A
        (CrystallineAffineDifferentials.comparison f U) (k + 1)).comp
      ((CrystallinePDDeRham.algebraicFamily A Γ(Y, U.1) k).comp
        (exteriorPower.form.mapRestrictScalars A
          (LinearEquiv.symm
            (LinearEquiv.ofBijective (CrystallineAffineDifferentials.comparison f U)
              (CrystallineAffineDifferentials.comparison_bijective f U))).toLinearMap k))

/-- Actual exterior multiplication by a relative one-form on an affine chart. -/
noncomputable def affineLeftWedge (k : ℕ) :
    Γ(oneForms f, U.1) →ₗ[Γ(Y, U.1)]
      exteriorPower.form Γ(Y, U.1) Γ(oneForms f, U.1) k →ₗ[Γ(Y, U.1)]
      exteriorPower.form Γ(Y, U.1) Γ(oneForms f, U.1) (k + 1) :=
  (Nat.add_comm 1 k) ▸ CrystallineFormWedge.wedge Γ(Y, U.1) Γ(oneForms f, U.1) 1 k

/-- Actual exterior multiplication by a relative two-form on an affine chart. -/
noncomputable def affineLeftWedgeTwo (k : ℕ) :
    exteriorPower.form Γ(Y, U.1) Γ(oneForms f, U.1) 2 →ₗ[Γ(Y, U.1)]
      exteriorPower.form Γ(Y, U.1) Γ(oneForms f, U.1) k →ₗ[Γ(Y, U.1)]
      exteriorPower.form Γ(Y, U.1) Γ(oneForms f, U.1) (k + 2) :=
  (Nat.add_comm 2 k) ▸ CrystallineFormWedge.wedge Γ(Y, U.1) Γ(oneForms f, U.1) 2 k

/-- The one-form wedge is the actual exterior multiplication, after identifying
`1 + k` with `k + 1`. -/
theorem affineLeftWedge_eq (k : ℕ) :
    affineLeftWedge f U k =
      (Nat.add_comm 1 k) ▸
        CrystallineFormWedge.wedge Γ(Y, U.1) Γ(oneForms f, U.1) 1 k :=
  sorry

/-- The two-form wedge is the actual exterior multiplication, after identifying
`2 + k` with `k + 2`. -/
theorem affineLeftWedgeTwo_eq (k : ℕ) :
    affineLeftWedgeTwo f U k =
      (Nat.add_comm 2 k) ▸
        CrystallineFormWedge.wedge Γ(Y, U.1) Γ(oneForms f, U.1) 2 k :=
  sorry

/-- The affine exterior calculus of relative differentials on a chart. -/
noncomputable def affineCalculus :=
  -- Local instance justification (noncanonical choice): the structure map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) :=
    (CrystallineAffineDifferentials.baseMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(oneForms f, U.1) :=
    Module.compHom _ (CrystallineAffineDifferentials.baseMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(oneForms f, U.1)
  (ExteriorCalculus.of (affineLeftWedge f U) (affineLeftWedgeTwo f U)
      (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry) (fun _ _ _ _ ↦ sorry) sorry :
    ExteriorCalculus (CrystallineAffineDifferentials.derivation f U)
      (affineFamily f U))

/-- Affine components of the higher de Rham differentials, obtained by the
Leibniz/wedge extension of the connection. -/
noncomputable def localSuccDifferential [Smooth f] [M.IsCoherent] (n : ℕ) :
    (baseTerm f M (n + 1)).obj.obj (op U.1) ⟶
      (baseTerm f M (n + 2)).obj.obj (op U.1) :=
  -- Local instance justification (noncanonical choice): the structure map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) :=
    (CrystallineAffineDifferentials.baseMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(oneForms f, U.1) :=
    Module.compHom _ (CrystallineAffineDifferentials.baseMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(oneForms f, U.1)
  let source := (baseTerm f M (n + 1)).obj.obj (op U.1)
  let target := (baseTerm f M (n + 2)).obj.obj (op U.1)
  @ModuleCat.ofHom A _ source target source.isAddCommGroup source.isModule
    target.isAddCommGroup target.isModule
    { toFun := fun m ↦
        (baseTermSectionsAddEquiv f M U (n + 2)).symm
          ((affineTermEquiv f M U (n + 2))
            (Connection.differential (affineConnection f M nabla U)
              (affineCalculus f U) (n + 1)
              ((affineTermEquiv f M U (n + 1)).symm
                ((baseTermSectionsAddEquiv f M U (n + 1)) m))))
      map_add' := sorry
      map_smul' := sorry }

/-- The affine components of higher de Rham differentials commute with restriction. -/
noncomputable def basisSuccDifferential [Smooth f] [M.IsCoherent] (n : ℕ) :
    (CrystallineAffineSheafExtension.affineInclusion Y).op ⋙
        (baseTerm f M (n + 1)).obj ⟶
      (CrystallineAffineSheafExtension.affineInclusion Y).op ⋙
        (baseTerm f M (n + 2)).obj where
  app V := localSuccDifferential f M nabla V.unop n
  naturality := sorry

/-- Higher sheaf de Rham differentials, uniquely extended from the affine
Leibniz/wedge components of the given connection. -/
noncomputable def sheafDifferential_succ [Smooth f] [M.IsCoherent] (n : ℕ) :
    baseTerm f M (n + 1) ⟶ baseTerm f M (n + 2) :=
  CrystallineAffineSheafExtension.extend Y (baseTerm f M (n + 1)) (baseTerm f M (n + 2))
    (basisSuccDifferential f M nabla n)

/-- Integrability of a sheaf connection is vanishing of the curvature
in the sheaf de Rham complex. -/
def IsIntegrable [Smooth f] [M.IsCoherent] : Prop :=
  sheafDifferential_zero f M nabla ≫ sheafDifferential_succ f M nabla 0 = 0

/-- Integrability is exactly vanishing of the degree-zero/one sheaf curvature. -/
theorem IsIntegrable_iff [Smooth f] [M.IsCoherent] :
    IsIntegrable f M nabla ↔
      sheafDifferential_zero f M nabla ≫ sheafDifferential_succ f M nabla 0 = 0 :=
  sorry

/-- The sheaf de Rham differential of `(M, nabla)` in every degree. Degree zero is
the connection itself; higher degrees are its Leibniz/wedge extension. -/
noncomputable def sheafDifferential [Smooth f] [M.IsCoherent] (n : ℕ) :
    baseTerm f M n ⟶ baseTerm f M (n + 1) :=
  match n with
  | 0 => sheafDifferential_zero f M nabla
  | n + 1 => sheafDifferential_succ f M nabla n

/-- Consecutive sheaf de Rham differentials compose to zero when the connection
is integrable. -/
theorem sheafDifferential_comp [Smooth f] [M.IsCoherent]
    (hInt : IsIntegrable f M nabla) (n : ℕ) :
    sheafDifferential f M nabla n ≫ sheafDifferential f M nabla (n + 1) = 0 :=
  sorry

/-- The degree-zero sheaf differential recovers the given connection. -/
theorem sheafDifferential_d_zero [Smooth f] [M.IsCoherent] :
    sheafDifferential f M nabla 0 =
      (CrystallineSheafDegreeBridges.baseDegreeZero f M).hom ≫
        nabla ≫ (CrystallineSheafDegreeBridges.baseDegreeOne f M).inv :=
  sorry

/-- The sheaf de Rham complex of a module with integrable connection on `Y / S`. -/
noncomputable def sheafComplex [Smooth f] [M.IsCoherent]
    (hInt : IsIntegrable f M nabla) :
    CochainComplex (TopCat.Sheaf (ModuleCat.{u} A) Y.toTopCat) ℕ :=
  CochainComplex.of (baseTerm f M) (sheafDifferential f M nabla)
    (sheafDifferential_comp f M nabla hInt)

/-- Derived global sections `RΓ(Y, M ⊗ Ω^•_{Y/S})` in `D(A)`. -/
noncomputable def deRhamSections [Smooth f] [M.IsCoherent]
    (hInt : IsIntegrable f M nabla)
    [HasSheafify (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian
      (Sheaf (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A))] :
    DerivedCategory (ModuleCat.{u + 1} A) :=
  CrystallineModuleDerivedSections.ofComplex A Y (sheafComplex f M nabla hInt)


end SheafDeRham
end CrystallineCompleteConnection
