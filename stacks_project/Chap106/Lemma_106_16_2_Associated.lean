/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Definition_96_11_1_QCoh

/-!
# Associated quasi-coherent modules on affine slices

For an affine scheme `U` over `S`, an `A`-module `M` with `A = Γ(U.left, ⊤)`
determines a quasi-coherent module on `slice U` by the rule `T ↦ M ⊗[A] Γ(T)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty Opposite
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}}

/-- The ring map `A → Γ(T)` induced by the structure morphism of an object of
`slice U`. -/
def associatedSectionHom (U : Over S) (x : (GroupoidsOver.slice U).totalᵒᵖ) :
    Γ(U.left, ⊤) →+* Γ(x.unop.left.left, ⊤) :=
  x.unop.hom.left.appTop.hom

/-- `associatedSectionHom` is `appTop` of the underlying scheme morphism. -/
theorem associatedSectionHom_eq (U : Over S)
    (x : (GroupoidsOver.slice U).totalᵒᵖ) :
    associatedSectionHom U x = x.unop.hom.left.appTop.hom :=
  rfl

/-- Scalar extension of an `A`-module along `associatedSectionHom`. -/
def associatedExtend (U : Over S) (M : ModuleCat.{u} Γ(U.left, ⊤))
    (x : (GroupoidsOver.slice U).totalᵒᵖ) :
    ModuleCat.{u} Γ(x.unop.left.left, ⊤) :=
  (ModuleCat.extendScalars (associatedSectionHom U x)).obj M

/-- `associatedExtend` is extension of scalars along `associatedSectionHom`. -/
theorem associatedExtend_eq (U : Over S) (M : ModuleCat.{u} Γ(U.left, ⊤))
    (x : (GroupoidsOver.slice U).totalᵒᵖ) :
    associatedExtend U M x =
      (ModuleCat.extendScalars (associatedSectionHom U x)).obj M :=
  rfl

/-- The ring map on global sections induced by a morphism of `slice U`. -/
def associatedRestrictRingHom (U : Over S)
    {x y : (GroupoidsOver.slice U).totalᵒᵖ} (f : x ⟶ y) :
    Γ(x.unop.left.left, ⊤) →+* Γ(y.unop.left.left, ⊤) :=
  f.unop.left.left.appTop.hom

/-- `associatedRestrictRingHom` is `appTop` of the underlying scheme morphism. -/
theorem associatedRestrictRingHom_eq (U : Over S)
    {x y : (GroupoidsOver.slice U).totalᵒᵖ} (f : x ⟶ y) :
    associatedRestrictRingHom U f = f.unop.left.left.appTop.hom :=
  rfl

/-- The `A`-linear map on section rings induced by a morphism of `slice U`. -/
def associatedRestrictLinear (U : Over S)
    {x y : (GroupoidsOver.slice U).totalᵒᵖ} (f : x ⟶ y) :=
  -- Local instance justification (proof-local temporary data): the `A`-algebra
  -- structures on section rings are induced by `associatedSectionHom`.
  letI := (associatedSectionHom U x).toAlgebra
  letI := (associatedSectionHom U y).toAlgebra
  (LinearMap.mk
      { toFun := associatedRestrictRingHom U f
        map_add' := map_add _ }
      (fun _ _ ↦ sorry) :
      Γ(x.unop.left.left, ⊤) →ₗ[Γ(U.left, ⊤)] Γ(y.unop.left.left, ⊤))

/-- Restriction of `associatedExtend` along a morphism of `slice U`. -/
def associatedPresheafMap (U : Over S) (M : ModuleCat.{u} Γ(U.left, ⊤))
    {x y : (GroupoidsOver.slice U).totalᵒᵖ} (f : x ⟶ y) :
    associatedExtend U M x ⟶
      (ModuleCat.restrictScalars
        ((GroupoidsOver.structureSheaf (GroupoidsOver.slice U)).obj.map f).hom).obj
        (associatedExtend U M y) :=
  -- Local instance justification (proof-local temporary data): the tensor
  -- product `Γ(T) ⊗[A] M` uses the `A`-algebra structure from
  -- `associatedSectionHom`.
  letI := (associatedSectionHom U x).toAlgebra
  letI := (associatedSectionHom U y).toAlgebra
  ModuleCat.homMk
    (AddCommGrpCat.ofHom
      { toFun := fun t ↦
          TensorProduct.map (associatedRestrictLinear U f)
            (LinearMap.id (R := Γ(U.left, ⊤))) t
        map_zero' := sorry
        map_add' := sorry })
    (fun _ ↦ sorry)

/-- The module presheaf `T ↦ M ⊗[A] Γ(T)` on the fppf site of `slice U`. -/
def associatedPresheaf (U : Over S) (M : ModuleCat.{u} Γ(U.left, ⊤)) :
    PresheafOfModules.{u}
      (GroupoidsOver.structureSheaf (GroupoidsOver.slice U)).obj where
  obj x := associatedExtend U M x
  map f := associatedPresheafMap U M f
  map_id _ := sorry
  map_comp _ _ := sorry

/-- Objectwise, `associatedPresheaf` is scalar extension along
`associatedSectionHom`. -/
theorem associatedPresheaf_obj (U : Over S) (M : ModuleCat.{u} Γ(U.left, ⊤))
    (x : (GroupoidsOver.slice U).totalᵒᵖ) :
    (associatedPresheaf U M).obj x = associatedExtend U M x :=
  rfl

/-- The morphism action of `associatedPresheaf` on an `A`-linear map. -/
def associatedPresheafHom (U : Over S) {M N : ModuleCat.{u} Γ(U.left, ⊤)}
    (φ : M ⟶ N) : associatedPresheaf U M ⟶ associatedPresheaf U N where
  app x := (ModuleCat.extendScalars (associatedSectionHom U x)).map φ
  naturality := sorry

/-- Modules on the fppf ringed site of `slice U` associated to `A`-modules. -/
def associatedModules (U : Over S) [IsAffine U.left] :
    ModuleCat.{u} Γ(U.left, ⊤) ⥤
      RingedSite.ModuleCat.{u} (fppfRingedSite (GroupoidsOver.slice U)) where
  obj M := { val := associatedPresheaf U M, isSheaf := sorry }
  map φ := { val := associatedPresheafHom U φ }
  map_id := sorry
  map_comp := sorry

/-- The underlying presheaf of `associatedModules` is `associatedPresheaf`. -/
theorem associatedModules_obj (U : Over S) [IsAffine U.left]
    (M : ModuleCat.{u} Γ(U.left, ⊤)) :
    ((associatedModules U).obj M).val = associatedPresheaf U M :=
  rfl

/-- Associated quasi-coherent modules on the slice of an affine scheme. -/
def associatedQCoh (U : Over S) [IsAffine U.left] :
    ModuleCat.{u} Γ(U.left, ⊤) ⥤ QCoh (GroupoidsOver.slice U) :=
  (quasiCoherentModuleProperty (GroupoidsOver.slice U)).lift
    (associatedModules U) (fun _ ↦ sorry)

/-- The underlying module sheaf of `associatedQCoh` is `associatedModules`. -/
theorem associatedQCoh_obj (U : Over S) [IsAffine U.left]
    (M : ModuleCat.{u} Γ(U.left, ⊤)) :
    ((associatedQCoh U).obj M).obj = (associatedModules U).obj M :=
  rfl

end AlgebraicGeometry.GroupoidsOver.QCoh
