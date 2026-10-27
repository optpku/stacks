/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.DeRham.Terms
public import ReasLib.AlgebraicGeometry.Scheme.Module.Differentials.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.AffineSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.DerivedSections
public import ReasLib.AlgebraicGeometry.Scheme.Sheaf.AffineBasis
public import ReasLib.RingTheory.Kaehler.DeRham.Connection
public import ReasLib.RingTheory.Kaehler.DeRham.Exterior
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.Calculus
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.LinearAlgebra.ExteriorPower.FormWedge
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Properties
public import ReasLib.CategoryTheory.Sites.ModuleSheafGrothendieck
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Sheaves.Functors


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules.DeRham

section SheafDeRham

variable {A : Type u} [CommRing A]
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
variable (M : Y.Modules)
variable (hcoh : M.IsCoherent)
variable (nabla : asBaseSheaf f M ⟶ asBaseSheaf f (oneFormTensor f M))

/-- The degree-zero sheaf differential is the given connection, transported
through the canonical exterior-degree identifications. -/
noncomputable def sheafDifferential_zero :
    baseTerm f M 0 ⟶ baseTerm f M 1 :=
  (AlgebraicGeometry.Scheme.Modules.DeRham.baseDegreeZero f M).hom ≫
    nabla ≫ (AlgebraicGeometry.Scheme.Modules.DeRham.baseDegreeOne f M).inv

variable (U : Y.affineOpens)




include hcoh in
/-- Algebraic tensors with exterior forms compare with sheaf de Rham terms. -/
theorem affineTermCompare_bijective [Smooth f] (n : ℕ) :
    Function.Bijective
      ((AlgebraicGeometry.Scheme.Modules.Affine.tensorMap U M (forms f n)).comp
        (TensorProduct.map
          (LinearMap.id : Γ(M, U.1) →ₗ[Γ(Y, U.1)] Γ(M, U.1))
          (AlgebraicGeometry.Scheme.Modules.Affine.exteriorMap U (oneForms f) n))) :=
  sorry

/-- The canonical additive identification of algebraic tensors with sheaf
de Rham terms on an affine open. -/
noncomputable def affineTermEquiv [Smooth f] (n : ℕ) :
    Γ(M, U.1) ⊗[Γ(Y, U.1)]
        exteriorPower.form Γ(Y, U.1) Γ(oneForms f, U.1) n ≃+
      Γ(term f M n, U.1) :=
  AddEquiv.ofBijective
    ((AlgebraicGeometry.Scheme.Modules.Affine.tensorMap U M (forms f n)).comp
      (TensorProduct.map
        (LinearMap.id : Γ(M, U.1) →ₗ[Γ(Y, U.1)] Γ(M, U.1))
        (AlgebraicGeometry.Scheme.Modules.Affine.exteriorMap U (oneForms f) n)))
    (affineTermCompare_bijective f M hcoh U n)



/-- The given sheaf connection as an additive map of affine sections. -/
noncomputable def affineNablaHom :
    Γ(M, U.1) →+ Γ(oneFormTensor f M, U.1) :=
  (nabla.hom.app (op U.1)).hom.toAddMonoidHom

include hcoh in
/-- Algebraic tensors with one-forms compare with `M ⊗ Ω_{Y/S}` sections. -/
theorem tensorOneForm_bijective [Smooth f] :
    Function.Bijective (AlgebraicGeometry.Scheme.Modules.Affine.tensorMap U M (oneForms f)) :=
  sorry

/-- The canonical identification `Γ(M) ⊗ Γ(Ω) ≃ Γ(M ⊗ Ω)` on an affine open. -/
noncomputable def tensorOneFormEquiv [Smooth f] :
    Γ(M, U.1) ⊗[Γ(Y, U.1)] Γ(oneForms f, U.1) ≃+ Γ(oneFormTensor f M, U.1) :=
  AddEquiv.ofBijective (AlgebraicGeometry.Scheme.Modules.Affine.tensorMap U M (oneForms f))
    (tensorOneForm_bijective f M hcoh U)

/-- A sheaf connection must satisfy the actual affine Leibniz identity.
A-linearity alone is insufficient: even the zero map generally fails this law. -/
def IsConnection : Prop :=
  ∀ (V : Y.affineOpens) (b : Γ(Y, V.1)) (m : Γ(M, V.1)),
    affineNablaHom f M nabla V (b • m) - b • affineNablaHom f M nabla V m =
      (SheafOfModules.RingedSite.tensorSection Y.sheaf (op V.1) m
        (AlgebraicGeometry.Scheme.RelativeDifferentials.Affine.sectionDerivation f V b) :
          Γ(oneFormTensor f M, V.1))

/-- The affine connection map `M → M ⊗ Ω` associated with the sheaf connection. -/
noncomputable def affineConnectionHom [Smooth f] :
    Γ(M, U.1) →+ Γ(M, U.1) ⊗[Γ(Y, U.1)] Γ(oneForms f, U.1) :=
  (tensorOneFormEquiv f M hcoh U).symm.toAddMonoidHom.comp (affineNablaHom f M nabla U)

variable (hConn : IsConnection f M nabla)

include hConn in
/-- The specified affine tensor comparison transfers the sheaf Leibniz law.
The hypothesis is retained; this is not asserted for arbitrary A-linear maps. -/
theorem affineConnection_leibniz [Smooth f]
    (b : Γ(Y, U.1)) (m : Γ(M, U.1)) :
    affineConnectionHom f M hcoh nabla U (b • m) =
      b • affineConnectionHom f M hcoh nabla U m +
        m ⊗ₜ[Γ(Y, U.1)] AlgebraicGeometry.Scheme.RelativeDifferentials.Affine.sectionDerivation f U b := sorry

/-- The affine connection packaged from the given sheaf morphism. -/
noncomputable def affineConnection [Smooth f] :=
  -- Local instance justification (noncanonical choice): the structure map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) :=
    (Scheme.Hom.sectionsMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(oneForms f, U.1) :=
    Module.compHom _ (Scheme.Hom.sectionsMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(oneForms f, U.1)
  (Connection.of (affineConnectionHom f M hcoh nabla U) (affineConnection_leibniz f M hcoh nabla U hConn) :
    Connection (AlgebraicGeometry.Scheme.RelativeDifferentials.Affine.derivation f U) Γ(M, U.1))

/-- The affine exterior-form differential family, transported from the
algebraic de Rham family along the canonical Kähler comparison. -/
noncomputable def affineFamily :=
  -- Local instance justification (noncanonical choice): the structure map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) :=
    (Scheme.Hom.sectionsMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(oneForms f, U.1) :=
    Module.compHom _ (Scheme.Hom.sectionsMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(oneForms f, U.1)
  fun k ↦
    (exteriorPower.form.mapRestrictScalars A
        (AlgebraicGeometry.Scheme.RelativeDifferentials.Affine.comparison f U) (k + 1)).comp
      ((CrystallinePDDeRham.algebraicFamily A Γ(Y, U.1) k).comp
        (exteriorPower.form.mapRestrictScalars A
          (LinearEquiv.symm
            (LinearEquiv.ofBijective (AlgebraicGeometry.Scheme.RelativeDifferentials.Affine.comparison f U)
              (AlgebraicGeometry.Scheme.RelativeDifferentials.Affine.comparison_bijective f U))).toLinearMap k))

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



/-- The affine exterior differential obeys the scalar Leibniz rule. -/
theorem affineFamily_smul :
  -- Local instance justification (noncanonical choice): the structure map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) :=
    (Scheme.Hom.sectionsMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(oneForms f, U.1) :=
    Module.compHom _ (Scheme.Hom.sectionsMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(oneForms f, U.1)
  ∀ (k : ℕ) (b : Γ(Y, U.1))
      (ω : exteriorPower.form Γ(Y, U.1) Γ(oneForms f, U.1) k),
    affineFamily f U k (b • ω) = affineLeftWedge f U k
      (AlgebraicGeometry.Scheme.RelativeDifferentials.Affine.derivation f U b) ω +
        b • affineFamily f U k ω := sorry

/-- The affine exterior differential obeys the graded one-form Leibniz rule. -/
theorem affineFamily_leftWedge :
  -- Local instance justification (noncanonical choice): the structure map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) :=
    (Scheme.Hom.sectionsMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(oneForms f, U.1) :=
    Module.compHom _ (Scheme.Hom.sectionsMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(oneForms f, U.1)
  ∀ (k : ℕ) (η : Γ(oneForms f, U.1))
      (ω : exteriorPower.form Γ(Y, U.1) Γ(oneForms f, U.1) k),
    affineFamily f U (k + 1) (affineLeftWedge f U k η ω) =
      affineLeftWedgeTwo f U k (affineFamily f U 1 η) ω -
        affineLeftWedge f U (k + 1) η (affineFamily f U k ω) := sorry

/-- Successive affine one-form wedges associate with the two-form wedge. -/
theorem affineLeftWedge_assoc :
  -- Local instance justification (noncanonical choice): the structure map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) :=
    (Scheme.Hom.sectionsMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(oneForms f, U.1) :=
    Module.compHom _ (Scheme.Hom.sectionsMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(oneForms f, U.1)
  ∀ (k : ℕ) (η ξ : Γ(oneForms f, U.1))
      (ω : exteriorPower.form Γ(Y, U.1) Γ(oneForms f, U.1) k),
    affineLeftWedge f U (k + 1) η (affineLeftWedge f U k ξ ω) =
      affineLeftWedgeTwo f U k (affineLeftWedge f U 1 η ξ) ω := sorry

/-- The affine exterior family is the de Rham differential of the relative derivation. -/
theorem affineFamily_isDifferential :
  -- Local instance justification (noncanonical choice): the structure map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) :=
    (Scheme.Hom.sectionsMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(oneForms f, U.1) :=
    Module.compHom _ (Scheme.Hom.sectionsMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(oneForms f, U.1)
  DifferentialOperator.DeRham.IsDifferential
    (AlgebraicGeometry.Scheme.RelativeDifferentials.Affine.derivation f U) (affineFamily f U) := sorry

/-- The affine exterior calculus of relative differentials on a chart. -/
noncomputable def affineCalculus :=
  -- Local instance justification (noncanonical choice): the structure map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) :=
    (Scheme.Hom.sectionsMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(oneForms f, U.1) :=
    Module.compHom _ (Scheme.Hom.sectionsMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(oneForms f, U.1)
  (ExteriorCalculus.of (affineLeftWedge f U) (affineLeftWedgeTwo f U)
      (affineFamily_smul f U) (affineFamily_leftWedge f U)
      (affineLeftWedge_assoc f U) (affineFamily_isDifferential f U) :
    ExteriorCalculus (AlgebraicGeometry.Scheme.RelativeDifferentials.Affine.derivation f U)
      (affineFamily f U))

/-- The affine higher differential preserves addition of sections. -/
theorem localSuccDifferential_add [Smooth f] (n : ℕ) :
  -- Local instance justification (noncanonical choice): the structure map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) :=
    (Scheme.Hom.sectionsMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(oneForms f, U.1) :=
    Module.compHom _ (Scheme.Hom.sectionsMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(oneForms f, U.1)
  let d : (baseTerm f M (n + 1)).obj.obj (op U.1) →
      (baseTerm f M (n + 2)).obj.obj (op U.1) :=
    fun m ↦
        ((affineTermEquiv f M hcoh U (n + 2))
            (Connection.differential (affineConnection f M hcoh nabla U hConn)
              (affineCalculus f U) (n + 1)
              ((affineTermEquiv f M hcoh U (n + 1)).symm m)))
  ∀ x y : (baseTerm f M (n + 1)).obj.obj (op U.1), d (x + y) = d x + d y := sorry

/-- The affine higher differential is linear over the base ring. -/
theorem localSuccDifferential_smul [Smooth f] (n : ℕ) :
  -- Local instance justification (noncanonical choice): the structure map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) :=
    (Scheme.Hom.sectionsMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(oneForms f, U.1) :=
    Module.compHom _ (Scheme.Hom.sectionsMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(oneForms f, U.1)
  let d : (baseTerm f M (n + 1)).obj.obj (op U.1) →
      (baseTerm f M (n + 2)).obj.obj (op U.1) :=
    fun m ↦
        ((affineTermEquiv f M hcoh U (n + 2))
            (Connection.differential (affineConnection f M hcoh nabla U hConn)
              (affineCalculus f U) (n + 1)
              ((affineTermEquiv f M hcoh U (n + 1)).symm m)))
  ∀ (a : A) (x : (baseTerm f M (n + 1)).obj.obj (op U.1)), d (a • x) = a • d x := sorry

/-- The affine higher differential as a base-linear morphism. -/
noncomputable def localSuccDifferential [Smooth f] (n : ℕ) :
    (baseTerm f M (n + 1)).obj.obj (op U.1) ⟶
      (baseTerm f M (n + 2)).obj.obj (op U.1) :=
  -- Local instance justification (noncanonical choice): the structure map f fixes this affine chart algebra.
  letI : Algebra A Γ(Y, U.1) :=
    (Scheme.Hom.sectionsMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): A acts on differential sections through that chart algebra.
  letI : Module A Γ(oneForms f, U.1) :=
    Module.compHom _ (Scheme.Hom.sectionsMap f U)
  -- Local instance justification (noncanonical choice): the restricted action forms the canonical tower for f.
  letI : IsScalarTower A Γ(Y, U.1) Γ(oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(oneForms f, U.1)
  let source := (baseTerm f M (n + 1)).obj.obj (op U.1)
  let target := (baseTerm f M (n + 2)).obj.obj (op U.1)
  @ModuleCat.ofHom A _ source target source.isAddCommGroup source.isModule
    target.isAddCommGroup target.isModule
    { toFun := fun m ↦
        ((affineTermEquiv f M hcoh U (n + 2))
            (Connection.differential (affineConnection f M hcoh nabla U hConn)
              (affineCalculus f U) (n + 1)
              ((affineTermEquiv f M hcoh U (n + 1)).symm m)))
      map_add' := localSuccDifferential_add f M hcoh nabla U hConn n
      map_smul' := localSuccDifferential_smul f M hcoh nabla U hConn n }

/-- The affine higher differentials commute with restriction between affine opens. -/
theorem basisSuccDifferential_naturality [Smooth f] (n : ℕ)
    {V W : (InducedCategory Y.Opens (fun U : Y.affineOpens ↦ U.1))ᵒᵖ} (i : V ⟶ W) :
    ((AlgebraicGeometry.Scheme.AffineSheaf.affineInclusion Y).op ⋙
        (baseTerm f M (n + 1)).obj).map i ≫
      localSuccDifferential f M hcoh nabla W.unop hConn n =
    localSuccDifferential f M hcoh nabla V.unop hConn n ≫
      ((AlgebraicGeometry.Scheme.AffineSheaf.affineInclusion Y).op ⋙
        (baseTerm f M (n + 2)).obj).map i := sorry

/-- The affine components of higher de Rham differentials commute with restriction. -/
noncomputable def basisSuccDifferential [Smooth f] (n : ℕ) :
    (AlgebraicGeometry.Scheme.AffineSheaf.affineInclusion Y).op ⋙
        (baseTerm f M (n + 1)).obj ⟶
      (AlgebraicGeometry.Scheme.AffineSheaf.affineInclusion Y).op ⋙
        (baseTerm f M (n + 2)).obj where
  app V := localSuccDifferential f M hcoh nabla V.unop hConn n
  naturality := fun _ _ i ↦ basisSuccDifferential_naturality f M hcoh nabla hConn n i

/-- Higher sheaf de Rham differentials, uniquely extended from the affine
Leibniz/wedge components of the given connection. -/
noncomputable def sheafDifferential_succ [Smooth f] (n : ℕ) :
    baseTerm f M (n + 1) ⟶ baseTerm f M (n + 2) :=
  AlgebraicGeometry.Scheme.AffineSheaf.extend Y (baseTerm f M (n + 1)) (baseTerm f M (n + 2))
    (basisSuccDifferential f M hcoh nabla hConn n)

/-- Integrability of a sheaf connection is vanishing of the curvature
in the sheaf de Rham complex. -/
def IsIntegrable [Smooth f] : Prop :=
  sheafDifferential_zero f M nabla ≫ sheafDifferential_succ f M hcoh nabla hConn 0 = 0


/-- The sheaf de Rham differential of `(M, nabla)` in every degree. Degree zero is
the connection itself; higher degrees are its Leibniz/wedge extension. -/
noncomputable def sheafDifferential [Smooth f] (n : ℕ) :
    baseTerm f M n ⟶ baseTerm f M (n + 1) :=
  match n with
  | 0 => sheafDifferential_zero f M nabla
  | n + 1 => sheafDifferential_succ f M hcoh nabla hConn n

/-- Consecutive sheaf de Rham differentials compose to zero when the connection
is integrable. -/
theorem sheafDifferential_comp [Smooth f]
    (hInt : IsIntegrable f M hcoh nabla hConn) (n : ℕ) :
    sheafDifferential f M hcoh nabla hConn n ≫ sheafDifferential f M hcoh nabla hConn (n + 1) = 0 :=
  sorry

/-- The degree-zero sheaf differential recovers the given connection. -/
theorem sheafDifferential_d_zero [Smooth f] :
    sheafDifferential f M hcoh nabla hConn 0 =
      (AlgebraicGeometry.Scheme.Modules.DeRham.baseDegreeZero f M).hom ≫
        nabla ≫ (AlgebraicGeometry.Scheme.Modules.DeRham.baseDegreeOne f M).inv :=
  sorry

/-- The sheaf de Rham complex of a module with integrable connection on `Y / S`. -/
noncomputable def sheafComplex [Smooth f]
    (hInt : IsIntegrable f M hcoh nabla hConn) :
    CochainComplex (TopCat.Sheaf (ModuleCat.{u} A) Y.toTopCat) ℕ :=
  CochainComplex.of (baseTerm f M) (sheafDifferential f M hcoh nabla hConn)
    (sheafDifferential_comp f M hcoh nabla hConn hInt)

/-- Derived global sections `RΓ(Y, M ⊗ Ω^•_{Y/S})` in `D(A)`. -/
noncomputable def deRhamSections [Smooth f]
    (hInt : IsIntegrable f M hcoh nabla hConn)
 :
    DerivedCategory (ModuleCat.{u + 1} A) :=
  @AlgebraicGeometry.Scheme.Modules.DerivedSections.ofComplex.{u, u + 1} A _ Y
    (CategoryTheory.GrothendieckTopology.moduleHasSheafify.{u, u, u, u + 1}
      (Opens.grothendieckTopology Y.toTopCat) A :
        HasSheafify (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A))
    (CategoryTheory.hasGlobalSectionsFunctor_of_hasTerminal
      (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A))
    (CategoryTheory.ModuleSheaf.isGrothendieckAbelian.{u, u, u, u + 1}
      (Opens.grothendieckTopology Y.toTopCat) A :
        IsGrothendieckAbelian.{u + 1}
          (Sheaf (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)))
    (sheafComplex f M hcoh nabla hConn hInt)


end SheafDeRham
end AlgebraicGeometry.Scheme.Modules.DeRham
