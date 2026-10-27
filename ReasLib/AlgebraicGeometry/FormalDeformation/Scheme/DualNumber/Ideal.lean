/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.DualNumber
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.KernelComparison
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

/-! # Coefficient ideals of dual-number scheme deformations -/

@[expose] public section
open CategoryTheory AlgebraicGeometry Functor Limits
open Functor.Fiber ArtinianLocalAlgCat
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Module.Associated AlgebraicGeometry.RingedSpace.Thickening
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry DualNumber
noncomputable section
universe u
variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeCat

/-- First-order thickening of `Spec k` along `k ⟶ k[ε]`. -/
abbrev residueThickening :
    (Spec (CommRingCat.of k)).toRingedSpace ⟶
      (Spec (CommRingCat.of (dualNumber Λ k).carrier)).toRingedSpace :=
  (specMap (dualNumberToResidue Λ k)).toShHom

/-- The source immersion of the trivial dual-number thickening is first-order. -/
instance instIsFirstOrderThickening_trivialSchemeImmersion (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    IsFirstOrderThickening
      ((trivialSchemeImmersion Λ k X hX).toShHom :
        X.toRingedSpace ⟶ (trivialScheme Λ k X hX).toRingedSpace) := sorry

/-- The dual-number thickening of `Spec k` is first-order. -/
instance instIsFirstOrderThickening_residue :
    IsFirstOrderThickening
      (residueThickening Λ k :
        (Spec (CommRingCat.of k)).toRingedSpace ⟶
          (Spec (CommRingCat.of (dualNumber Λ k).carrier)).toRingedSpace) := sorry

/-- The kernel of the coefficient projection `k[ε] ⟶ k`. -/
abbrev dualNumberKernel : Type u :=
  RingHom.ker (AlgHom.toRingHom (dualNumberToResidue Λ k).hom)

/-- Scalar multiplication on `ker(k[ε] ⟶ k)` through the residue field. -/
instance instModule_dualNumberKernel : Module k (dualNumberKernel Λ k)  :=
  let act : k → dualNumberKernel Λ k → dualNumberKernel Λ k :=
    fun r x ↦ ⟨⟨0, r * x.1.snd⟩, rfl⟩
  let laws : (∀ x, act 1 x = x) ∧
      (∀ r s x, act (r * s) x = act r (act s x)) ∧
      (∀ r, act r 0 = 0) ∧
      (∀ r x y, act r (x + y) = act r x + act r y) ∧
      (∀ r s x, act (r + s) x = act r x + act s x) ∧
      (∀ x, act 0 x = 0) := sorry
  { smul := act
    one_smul := laws.1
    mul_smul := laws.2.1
    smul_zero := laws.2.2.1
    smul_add := laws.2.2.2.1
    add_smul := laws.2.2.2.2.1
    zero_smul := laws.2.2.2.2.2 }

/-- ε-coefficient identification `ker(k[ε] ⟶ k) ≃ k`. -/
def dualNumberKernelEquiv : dualNumberKernel Λ k ≃ₗ[k] k  :=
  let forward : dualNumberKernel Λ k → k := fun x ↦ x.1.snd
  let backward : k → dualNumberKernel Λ k := fun c ↦ ⟨⟨0, c⟩, rfl⟩
  let laws : Function.LeftInverse backward forward ∧ Function.RightInverse backward forward ∧
      (∀ x y, forward (x + y) = forward x + forward y) ∧
      (∀ (r : k) x, forward (r • x) = r • forward x) := sorry
  { toFun := forward
    invFun := backward
    left_inv := laws.1
    right_inv := laws.2.1
    map_add' := laws.2.2.1
    map_smul' := laws.2.2.2 }

/-- Associated sheaf of the dual-number kernel through `hX`. -/
def associatedDualNumberKernel (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    X.toRingedSpace.Modules :=
  obj (Scheme.Hom.globalSectionsMap hX)
    (ModuleCat.of k (dualNumberKernel Λ k))

/-- Canonical isomorphism `Associated(ker(k[ε] ⟶ k)) ≅ O_X` via ε-coefficients. -/
def associatedKernelIsoUnit (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    associatedDualNumberKernel Λ k X hX ≅
      SheafOfModules.unit X.toRingedSpace.ringCatSheaf :=
  (functor (Scheme.Hom.globalSectionsMap hX)).mapIso
      (LinearEquiv.toModuleIso (dualNumberKernelEquiv Λ k)) ≪≫
    (functor (Scheme.Hom.globalSectionsMap hX)).mapIso (Iso.refl _) ≪≫
    (unitIso (Scheme.Hom.globalSectionsMap hX)).symm ≪≫
    (unitIsoTensorUnit X.toRingedSpace).symm

/-- Comparison `Ker(Spec k → Spec k[ε]) ⟶ hX_* Ker(X → X')` of the cartesian structure square. -/
def structureKernelMap (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    idealModule (residueThickening Λ k) ⟶
      ((hX.toShHom) _*).obj (idealModule ((trivialSchemeImmersion Λ k X hX).toShHom)) :=
  kernelMapOf (residueThickening Λ k) (hX.toShHom)
    ((trivialSchemeImmersion Λ k X hX).toShHom) inferInstance
    ((trivialSchemeOver Λ k X hX).toShHom) sorry

/-- Adjunct `hX^* Ker(Spec k → Spec k[ε]) ⟶ Ker(X → X')` of `structureKernelMap`. -/
def structureKernelPull (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    ((hX.toShHom) ^*).obj (idealModule (residueThickening Λ k)) ⟶
      idealModule ((trivialSchemeImmersion Λ k X hX).toShHom) :=
  cPull (residueThickening Λ k) (hX.toShHom) (structureKernelMap Λ k X hX)

/-- The structure-square kernel comparison `hX^* Ker(Spec k → Spec k[ε]) ⟶ Ker(X → X')`
is an isomorphism because the trivial dual-number square is cartesian. -/
instance instIsIso_structureKernelPull (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    IsIso (structureKernelPull Λ k X hX) := sorry

/-- Associated sheaf of `ker(k[ε] ⟶ k)` on `Spec k`. -/
abbrev residueAssociatedKernel :
    (Spec (CommRingCat.of k)).toRingedSpace.Modules :=
  associatedDualNumberKernel Λ k (Spec (CommRingCat.of k)) (𝟙 _)

/-- ε-coefficient isomorphism `Associated(ker) ≅ O_{Spec k}`. -/
def residueAssociatedIsoUnit :
    residueAssociatedKernel Λ k ≅
      SheafOfModules.unit (Spec (CommRingCat.of k)).toRingedSpace.ringCatSheaf :=
  associatedKernelIsoUnit Λ k (Spec (CommRingCat.of k)) (𝟙 _)

/-- The ideal of the coefficient thickening maps to its structure sheaf by extraction
of the ε coefficient. -/
def residueKernelToUnit :
    idealModule (residueThickening Λ k) ⟶
      SheafOfModules.unit (Spec (CommRingCat.of k)).toRingedSpace.ringCatSheaf :=
  let t := residueThickening Λ k
  let M := kernelIdealSheaf t
  let N := SheafOfModules.unit (Spec (CommRingCat.of k)).toRingedSpace.ringCatSheaf
  let raw : ∀ U, M.val.obj U → ((t _*).obj N).val.obj U := fun U x ↦
    @dite _ (U.unop = ⊤) (Classical.propDecidable _) (fun hU ↦
      let a := (Scheme.ΓSpecIso (CommRingCat.of (dualNumber Λ k).carrier)).hom
        ((Spec (CommRingCat.of (dualNumber Λ k).carrier)).presheaf.map
          (eqToHom hU.symm).op ((kernelIdealι t).val.app U x))
      (Spec (CommRingCat.of k)).presheaf.map
        (TopologicalSpace.Opens.leTop ((TopologicalSpace.Opens.map t.hom.base).obj U.unop)).op
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a.snd))
      (fun _ ↦ 0)
  let laws : (∀ U, raw U 0 = 0 ∧ ∀ x y, raw U (x + y) = raw U x + raw U y) ∧
      (∀ {U V} (i : U ⟶ V) x,
        raw V (M.val.map i x) = ((t _*).obj N).val.map i (raw U x)) ∧
      (∀ U r x, raw U (r • x) =
        @SMul.smul ((Spec (CommRingCat.of k)).presheaf.obj
          (Opposite.op ((TopologicalSpace.Opens.map t.hom.base).obj U.unop)))
          (N.val.obj (Opposite.op ((TopologicalSpace.Opens.map t.hom.base).obj U.unop)))
          inferInstance (t.hom.c.app U r) (raw U x)) := sorry
  let g : M ⟶ (t _*).obj N :=
    { val := PresheafOfModules.homMk
        { app U := AddCommGrpCat.ofHom
            { toFun := raw U
              map_zero' := (laws.1 U).1
              map_add' := (laws.1 U).2 }
          naturality := fun U V i ↦ AddCommGrpCat.hom_ext
            (AddMonoidHom.ext (fun x ↦ laws.2.1 i x)) }
        laws.2.2 }
  ((pullbackPushforwardAdjunction t).homEquiv M N).symm g

/-- Multiplication by ε, pulled back to the residue spectrum, inserts sections into
the coefficient thickening ideal. -/
def residueUnitToKernel :
    SheafOfModules.unit (Spec (CommRingCat.of k)).toRingedSpace.ringCatSheaf ⟶
      idealModule (residueThickening Λ k) :=
  let t := residueThickening Λ k
  let S := (Spec (CommRingCat.of k)).toRingedSpace
  let S' := (Spec (CommRingCat.of (dualNumber Λ k).carrier)).toRingedSpace
  let epsilonSection := (Scheme.ΓSpecIso (CommRingCat.of (dualNumber Λ k).carrier)).inv ⟨0, 1⟩
  let m := GlobalSections.mul (X := S') epsilonSection (SheafOfModules.unit S'.ringCatSheaf)
  let law : m ≫ SheafOfModules.RingedSite.KernelIdeal.map
      (commRingSheafPushforwardMap t) = 0 := sorry
  let g := kernel.lift _ m law ≫
    (kernelSubobjectIso (SheafOfModules.RingedSite.KernelIdeal.map
      (commRingSheafPushforwardMap t))).inv
  (unitIsoTensorUnit S).hom ≫ (pullbackUnitIso t).inv ≫
    (t ^*).map (unitIsoTensorUnit S').inv ≫ (t ^*).map g

/-- Extraction of the ε coefficient and insertion of an ε multiple identify the
coefficient thickening ideal with the structure module. -/
def residueKernelIsoUnit :
    idealModule (residueThickening Λ k) ≅
      SheafOfModules.unit (Spec (CommRingCat.of k)).toRingedSpace.ringCatSheaf :=
  let laws : residueKernelToUnit Λ k ≫ residueUnitToKernel Λ k = 𝟙 _ ∧
      residueUnitToKernel Λ k ≫ residueKernelToUnit Λ k = 𝟙 _ := sorry
  { hom := residueKernelToUnit Λ k
    inv := residueUnitToKernel Λ k
    hom_inv_id := laws.1
    inv_hom_id := laws.2 }

/-- The coefficient thickening ideal identifies with the associated kernel module. -/
def residueKernelIsoAssociated :
    idealModule (residueThickening Λ k) ≅ residueAssociatedKernel Λ k :=
  residueKernelIsoUnit Λ k ≪≫ (residueAssociatedIsoUnit Λ k).symm

/-- Pullback of `Associated_{Spec k}(ker)` along `hX` is `Associated_X(ker)`. -/
def associatedKernelPullbackIso (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    ((hX.toShHom) ^*).obj (residueAssociatedKernel Λ k) ≅
      associatedDualNumberKernel Λ k X hX :=
  obj.pullbackIso (hX.toShHom)
    (Scheme.Hom.globalSectionsMap (𝟙 (Spec (CommRingCat.of k))))
    (ModuleCat.of k (dualNumberKernel Λ k))

/-- Identification of the kernel of the trivial source thickening with `O_X`,
obtained by composing `structureKernelPull` with the ε-coefficient iso
`ker(k[ε] ⟶ k) ≃ k` and the associated-sheaf unit. -/
def trivialKernelIsoUnit (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    idealModule ((trivialSchemeImmersion Λ k X hX).toShHom) ≅
      SheafOfModules.unit X.toRingedSpace.ringCatSheaf :=
  (asIso (structureKernelPull Λ k X hX)).symm ≪≫
    ((hX.toShHom) ^*).mapIso (residueKernelIsoAssociated Λ k) ≪≫
    associatedKernelPullbackIso Λ k X hX ≪≫
    associatedKernelIsoUnit Λ k X hX

/-- Closed immersion of `X` into a dual-number deformation of `X`. -/
def immersionOf (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    X ⟶ (fiberInclusion.obj x).left.scheme :=
  (fiberInclusion.obj x).hom.schemeHom

/-- A source dual-number immersion is a first-order thickening. -/
instance instIsFirstOrderThickening_immersionOf (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    IsFirstOrderThickening ((immersionOf Λ k X hX x).toShHom) := sorry

/-- Dual-number thickening of `Spec k` with codomain the spectrum of a fibre object's base. -/
def fiberResidueThickening (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    (Spec (CommRingCat.of k)).toRingedSpace ⟶
      (Spec (CommRingCat.of (fiberInclusion.obj x).left.base.carrier)).toRingedSpace :=
  residueThickening Λ k ≫
    eqToHom
      (congrArg (fun A : ArtinianLocalAlgCat Λ k ↦
        (Spec (CommRingCat.of A.carrier)).toRingedSpace) x.property.symm)

/-- Dual-number thickenings of `Spec k` attached to fibre objects are first-order. -/
instance instIsFirstOrderThickening_fiberResidueThickening
    (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    IsFirstOrderThickening (fiberResidueThickening Λ k X hX x) := sorry

/-- Comparison `Ker(Spec k → Spec k[ε]) ⟶ hX_* Ker(X → X_ε)` of a dual-number fibre. -/
def fiberStructureKernelMap (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    idealModule (fiberResidueThickening Λ k X hX x) ⟶
      ((hX.toShHom) _*).obj (idealModule ((immersionOf Λ k X hX x).toShHom)) :=
  kernelMapOf (fiberResidueThickening Λ k X hX x) (hX.toShHom)
    ((immersionOf Λ k X hX x).toShHom) inferInstance
    ((fiberInclusion.obj x).left.structureHom.toShHom) sorry

/-- Adjunct of `fiberStructureKernelMap`. -/
def fiberStructureKernelPull (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    ((hX.toShHom) ^*).obj (idealModule (fiberResidueThickening Λ k X hX x)) ⟶
      idealModule ((immersionOf Λ k X hX x).toShHom) :=
  cPull (fiberResidueThickening Λ k X hX x) (hX.toShHom)
    (fiberStructureKernelMap Λ k X hX x)

/-- The fibrewise structure-square kernel comparison is an isomorphism. -/
instance instIsIso_fiberStructureKernelPull (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    IsIso (fiberStructureKernelPull Λ k X hX x) := sorry

/-- Comparison of kernel ideals along the fibre base identification
`fiberResidueThickening = residueThickening ≫ eqToHom`. -/
def fiberResidueKernelIso (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    idealModule (fiberResidueThickening Λ k X hX x) ≅
      idealModule (residueThickening Λ k)  :=
  let e := congrArg (fun A : ArtinianLocalAlgCat Λ k ↦
      (Spec (CommRingCat.of A.carrier)).toRingedSpace) x.property
  let forward := idealMap (eqToHom e.symm) rfl
  let laws : (fiberResidueThickening Λ k X hX x ≫ eqToHom e =
        residueThickening Λ k) ∧
      (∀ h : fiberResidueThickening Λ k X hX x ≫ eqToHom e = residueThickening Λ k,
        forward ≫ idealMap (eqToHom e) h = 𝟙 _ ∧
        idealMap (eqToHom e) h ≫ forward = 𝟙 _) := sorry
  { hom := forward
    inv := idealMap (eqToHom e) laws.1
    hom_inv_id := (laws.2 laws.1).1
    inv_hom_id := (laws.2 laws.1).2 }

/-- Identification of the kernel of a source dual-number thickening with `O_X`,
obtained by composing `fiberStructureKernelPull` with the ε-coefficient iso
`ker(k[ε] ⟶ k) ≃ k` and the associated-sheaf unit. -/
def immersionKernelIsoUnit (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    idealModule ((immersionOf Λ k X hX x).toShHom) ≅
      SheafOfModules.unit X.toRingedSpace.ringCatSheaf :=
  (asIso (fiberStructureKernelPull Λ k X hX x)).symm ≪≫
    ((hX.toShHom) ^*).mapIso (fiberResidueKernelIso Λ k X hX x) ≪≫
    ((hX.toShHom) ^*).mapIso (residueKernelIsoAssociated Λ k) ≪≫
    associatedKernelPullbackIso Λ k X hX ≪≫
    associatedKernelIsoUnit Λ k X hX

end FlatSchemeCat
