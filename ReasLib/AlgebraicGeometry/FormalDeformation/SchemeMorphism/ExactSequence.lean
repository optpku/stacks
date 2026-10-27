/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.DualNumber.Ideal
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.MapObstruction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.CategoryTheory.DerivedCategory.Ext

/-! # The infinitesimal exact sequence of a scheme morphism -/

@[expose] public section
open CategoryTheory AlgebraicGeometry Functor Limits
open Functor.Fiber ArtinianLocalAlgCat
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open scoped AlgebraicGeometry DerivedExt DualNumber RingedSpaceDerivedPullback
noncomputable section
universe u
variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeMorphismCat

variable {Λ k}

/-- Derivations `Der_k(O_Y, f_* O_X)`, realized as `Hom_{O_Y}(Ω_{Y/k}, f_* O_X)`. -/
abbrev derivations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) : Type u :=
  Ω[hY.toShHom] ⟶ ((f.toShHom _*).obj (SheafOfModules.unit X.toRingedSpace.ringCatSheaf))

/-- Scalar multiplication on `Hom(Ω_{Y/k}, f_* O_X)` by postcomposition with multiplication
by the global function induced by `c` through `hY`. -/
def smulDerivations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) (c : k) (α : derivations f hY) :
    derivations f hY :=
  α ≫ GlobalSections.mul (Scheme.Hom.globalSectionsMap hY c)
    ((f.toShHom _*).obj (SheafOfModules.unit X.toRingedSpace.ringCatSheaf))

/-- `k`-vector space structure on `Der_k(O_Y, f_* O_X)`. -/
instance instModule_derivations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) : Module k (derivations f hY) :=
  let act := smulDerivations f hY
  let laws : (∀ x, act 1 x = x) ∧
      (∀ x, act 0 x = 0) ∧ (∀ r, act r 0 = 0) ∧
      (∀ r x y, act r (x + y) = act r x + act r y) ∧
      (∀ r s x, act (r + s) x = act r x + act s x) ∧
      (∀ r s x, act (r * s) x = act r (act s x)) := sorry
  { smul := act
    one_smul := laws.1
    zero_smul := laws.2.1
    smul_zero := laws.2.2.1
    smul_add := laws.2.2.2.1
    add_smul := laws.2.2.2.2.1
    mul_smul := laws.2.2.2.2.2 }

/-- The obstruction space `Ext¹_{O_X}(Lf^* NL_{Y/k}, O_X)`. -/
abbrev obstructionSpace {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) : Type (u + 1) :=
  Ext⁽(1 : ℤ)⁾((modulePullbackDerived (f.toShHom)).obj
      (DerivedCategory.Q.obj (NL[hY.toShHom])),
    DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)))

/-- Scalar multiplication on the obstruction space by postcomposition with multiplication
by the global function induced by `c` through `hX = f ≫ hY`. -/
def smulObstruction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) (c : k) (x : obstructionSpace f hY) :
    obstructionSpace f hY :=
  x ≫ (shiftFunctor _ (1 : ℤ)).map
    (DerivedCategory.Q.map
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).map
        (GlobalSections.mul (Scheme.Hom.globalSectionsMap (f ≫ hY) c)
          (SheafOfModules.unit X.toRingedSpace.ringCatSheaf))))

/-- `k`-vector space structure on `Ext¹_{O_X}(Lf^* NL_{Y/k}, O_X)`. -/
instance instModule_obstructionSpace {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) : Module k (obstructionSpace f hY) :=
  let act := smulObstruction f hY
  let laws : (∀ x, act 1 x = x) ∧
      (∀ x, act 0 x = 0) ∧ (∀ r, act r 0 = 0) ∧
      (∀ r x y, act r (x + y) = act r x + act r y) ∧
      (∀ r s x, act (r + s) x = act r x + act s x) ∧
      (∀ r s x, act (r * s) x = act r (act s x)) := sorry
  { smul := act
    one_smul := laws.1
    zero_smul := laws.2.1
    smul_zero := laws.2.2.1
    smul_add := laws.2.2.2.1
    add_smul := laws.2.2.2.2.1
    mul_smul := laws.2.2.2.2.2 }

variable (Λ k)

/-- The commutative first-order cube of the trivial dual-number lift of `f`. -/
private theorem trivialCommDiagram {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    CommDiagram
      ((FlatSchemeCat.trivialSchemeImmersion Λ k X hX).toShHom) (hX.toShHom)
      ((FlatSchemeCat.trivialSchemeOver Λ k X hX).toShHom) (FlatSchemeCat.residueThickening Λ k)
      ((FlatSchemeCat.trivialSchemeImmersion Λ k Y hY).toShHom) (hY.toShHom)
      ((FlatSchemeCat.trivialSchemeOver Λ k Y hY).toShHom) (FlatSchemeCat.residueThickening Λ k)
      (f.toShHom) (𝟙 _) (𝟙 _) := sorry

/-- Canonical comparison of kernel ideals along `f` for the trivial dual-number cube. -/
def trivialKernelMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k)) (hf : f ≫ hY = hX) :
    idealModule ((FlatSchemeCat.trivialSchemeImmersion Λ k Y hY).toShHom) ⟶
      ((f.toShHom) _*).obj (idealModule ((FlatSchemeCat.trivialSchemeImmersion Λ k X hX).toShHom)) :=
  kernelMapOf ((FlatSchemeCat.trivialSchemeImmersion Λ k Y hY).toShHom) (f.toShHom)
    ((FlatSchemeCat.trivialSchemeImmersion Λ k X hX).toShHom) inferInstance
    ((trivialHom Λ k f hX hY hf).toShHom) sorry

/-- The relative first-order diagram of the trivial dual-number lift of `f`. -/
@[no_expose] def trivialRelativeDiagram {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    RelativeDiagram
      ((FlatSchemeCat.trivialSchemeImmersion Λ k X hX).toShHom) (hX.toShHom)
      ((FlatSchemeCat.trivialSchemeOver Λ k X hX).toShHom) (FlatSchemeCat.residueThickening Λ k)
      ((FlatSchemeCat.trivialSchemeImmersion Λ k Y hY).toShHom) (hY.toShHom)
      ((FlatSchemeCat.trivialSchemeOver Λ k Y hY).toShHom) (FlatSchemeCat.residueThickening Λ k)
      (f.toShHom) (𝟙 _) (𝟙 _) :=
  RelativeDiagram.of (trivialCommDiagram Λ k f hX hY hf)
    (trivialKernelMap Λ k f hX hY hf) sorry

/-- The trivial lift `f'` as a fitting map of `trivialRelativeDiagram`. -/
def trivialFittingMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    FittingMap (trivialRelativeDiagram Λ k f hX hY hf) :=
  let D := trivialRelativeDiagram Λ k f hX hY hf
  let g := (trivialHom Λ k f hX hY hf).toShHom
  let iX := (FlatSchemeCat.trivialSchemeImmersion Λ k X hX).toShHom
  let iY := (FlatSchemeCat.trivialSchemeImmersion Λ k Y hY).toShHom
  let laws : (iX ≫ g = f.toShHom ≫ iY) ∧
      (g ≫ (FlatSchemeCat.trivialSchemeOver Λ k Y hY).toShHom =
        (FlatSchemeCat.trivialSchemeOver Λ k X hX).toShHom ≫ 𝟙 _) ∧
      (∀ h : iX ≫ g = f.toShHom ≫ iY,
        kernelMapOf iY f.toShHom iX inferInstance g h = D.ν) := sorry
  FittingMap.of g laws.1 laws.2.1 (laws.2.2 laws.1)

/-- The conjugated morphism `β⁻¹ ∘ f' ∘ α` of trivial dual-number thickenings. -/
def conjugatedHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (p : (FlatSchemeCat.inf Λ k X hX × FlatSchemeCat.inf Λ k Y hY)) :
    FlatSchemeCat.trivialScheme Λ k X hX ⟶ FlatSchemeCat.trivialScheme Λ k Y hY :=
  (fiberInclusion.map p.1.val.hom).schemeHom ≫ trivialHom Λ k f hX hY hf ≫
    (fiberInclusion.map p.2.val.inv).schemeHom

/-- The conjugated morphism as a fitting map of the trivial dual-number cube. -/
def conjugatedFittingMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (p : (FlatSchemeCat.inf Λ k X hX × FlatSchemeCat.inf Λ k Y hY)) :
    FittingMap (trivialRelativeDiagram Λ k f hX hY hf) :=
  let D := trivialRelativeDiagram Λ k f hX hY hf
  let g := (conjugatedHom Λ k f hX hY hf p).toShHom
  let iX := (FlatSchemeCat.trivialSchemeImmersion Λ k X hX).toShHom
  let iY := (FlatSchemeCat.trivialSchemeImmersion Λ k Y hY).toShHom
  let laws : (iX ≫ g = f.toShHom ≫ iY) ∧
      (g ≫ (FlatSchemeCat.trivialSchemeOver Λ k Y hY).toShHom =
        (FlatSchemeCat.trivialSchemeOver Λ k X hX).toShHom ≫ 𝟙 _) ∧
      (∀ h : iX ≫ g = f.toShHom ≫ iY,
        kernelMapOf iY f.toShHom iX inferInstance g h = D.ν) := sorry
  FittingMap.of g laws.1 laws.2.1 (laws.2.2 laws.1)

/-- Transport `Hom(Ω_{Y/k}, f_* Ker(X → X'))` to `Hom(Ω_{Y/k}, f_* O_X)`. -/
def homKernelToDerivations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (α : Ω[hY.toShHom] ⟶
      ((f.toShHom) _*).obj (idealModule ((FlatSchemeCat.trivialSchemeImmersion Λ k X hX).toShHom))) :
    derivations f hY :=
  α ≫ ((f.toShHom) _*).map (FlatSchemeCat.trivialKernelIsoUnit Λ k X hX).hom

/-- Transport a derivation into a kernel-valued Hom via `FlatSchemeCat.trivialKernelIsoUnit.inv`. -/
def derivationsToHomKernel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (α : derivations f hY) :
    Ω[hY.toShHom] ⟶ ((f.toShHom) _*).obj (idealModule ((FlatSchemeCat.trivialSchemeImmersion Λ k X hX).toShHom)) :=
  α ≫ ((f.toShHom) _*).map (FlatSchemeCat.trivialKernelIsoUnit Λ k X hX).inv

/-- The connecting map `Inf(Def_X) × Inf(Def_Y) ⟶ Der_k(O_Y, f_* O_X)` sending
`(α, β)` to the difference of `f'` and `β⁻¹ ∘ f' ∘ α`. -/
def prodInfToDer {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    (FlatSchemeCat.inf Λ k X hX × FlatSchemeCat.inf Λ k Y hY) →ₗ[k] derivations f hY :=
  let g := fun p ↦
    homKernelToDerivations Λ k f hX hY
      (FittingMap.diff (trivialFittingMap Λ k f hX hY hf)
        (conjugatedFittingMap Λ k f hX hY hf p))
  let laws : IsLinearMap k g := sorry
  IsLinearMap.mk' g laws

/-- `prodInfToDer` is the difference of `f'` and the conjugated morphism. -/
theorem prodInfToDer_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (p : (FlatSchemeCat.inf Λ k X hX × FlatSchemeCat.inf Λ k Y hY)) :
    prodInfToDer Λ k f hX hY hf p =
      homKernelToDerivations Λ k f hX hY
        (FittingMap.diff (trivialFittingMap Λ k f hX hY hf)
          (conjugatedFittingMap Λ k f hX hY hf p)) := sorry

/-- The locally ringed space morphism obtained by perturbing `f'` by a derivation. -/
def perturbedLRSHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (α : derivations f hY) :
    (FlatSchemeCat.trivialScheme Λ k X hX).toLocallyRingedSpace ⟶
      (FlatSchemeCat.trivialScheme Λ k Y hY).toLocallyRingedSpace :=
  LocallyRingedSpace.homMk
    (FittingMap.perturb (derivationsToHomKernel Λ k f hX hY α)
      (trivialFittingMap Λ k f hX hY hf)).hom sorry

/-- The scheme morphism `X' ⟶ Y'` underlying a perturbed fitting map. -/
def perturbedSchemeHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (α : derivations f hY) :
    FlatSchemeCat.trivialScheme Λ k X hX ⟶ FlatSchemeCat.trivialScheme Λ k Y hY :=
  Scheme.Hom.mk (perturbedLRSHom Λ k f hX hY hf α)

/-- Dual-number object of `FlatSchemeMorphismCat` obtained by perturbing `f'` by a derivation. -/
def perturbedObj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (α : derivations f hY) : FlatSchemeMorphismCat Λ k :=
  of (dualNumber Λ k) (FlatSchemeCat.trivialScheme Λ k X hX) (FlatSchemeCat.trivialScheme Λ k Y hY)
    (perturbedSchemeHom Λ k f hX hY hf α)
    (FlatSchemeCat.trivialSchemeOver Λ k X hX) (FlatSchemeCat.trivialSchemeOver Λ k Y hY) sorry

/-- The slice arrow of a derivation-perturbed lift toward the residue object. -/
def perturbedLiftHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (α : derivations f hY) :
    perturbedObj Λ k f hX hY hf α ⟶
      fiberInclusion.obj (residueObj Λ k X Y f hX hY hf) :=
  let iX := FlatSchemeCat.trivialSchemeImmersion Λ k X hX
  let iY := FlatSchemeCat.trivialSchemeImmersion Λ k Y hY
  let laws : IsPullback iX f (perturbedSchemeHom Λ k f hX hY hf α) iY ∧
      IsPullback iY hY (FlatSchemeCat.trivialSchemeOver Λ k Y hY)
        (specMap (dualNumberToResidue Λ k)) := sorry
  Hom.of (dualNumberToResidue Λ k) iX iY laws.1 laws.2

/-- The slice object of a derivation-perturbed lift. -/
def perturbedLift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (α : derivations f hY) :
    (deformationForget Λ k X Y f hX hY hf).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ k X Y f hX hY hf).obj
        (Over.mk (perturbedLiftHom Λ k f hX hY hf α)) =
      dualNumber Λ k)

/-- The connecting map `Der_k(O_Y, f_* O_X) ⟶ T Def_{X ⟶ Y}` sending a derivation to the
isomorphism class of the perturbed morphism `f_ε`. -/
def derToTangent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    derivations f hY →ₗ[k] tangentSpace Λ k f hX hY hf :=
  let g : derivations f hY → tangentSpace Λ k f hX hY hf :=
    fun α ↦ Functor.tangentSpace.mk (deformationForget Λ k X Y f hX hY hf)
      (perturbedLift Λ k f hX hY hf α)
  let laws : IsLinearMap k g := sorry
  IsLinearMap.mk' g laws

/-- `derToTangent` sends a derivation to the class of the corresponding perturbed lift. -/
theorem derToTangent_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (α : derivations f hY) :
    derToTangent Λ k f hX hY hf α =
      Functor.tangentSpace.mk (deformationForget Λ k X Y f hX hY hf)
        (perturbedLift Λ k f hX hY hf α) := sorry

/-- Relative first-order diagram comparing deformations `X_ε` and `Y_ε` of `X` and `Y`. -/
def pairRelativeDiagram {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k))
    (y : (FlatSchemeCat.deformationForget Λ k Y hY).Fiber (dualNumber Λ k)) :
    RelativeDiagram
      ((FlatSchemeCat.immersionOf Λ k X hX x).toShHom) (hX.toShHom)
      ((fiberInclusion.obj x).left.structureHom.toShHom)
      (FlatSchemeCat.fiberResidueThickening Λ k X hX x)
      ((FlatSchemeCat.immersionOf Λ k Y hY y).toShHom) (hY.toShHom)
      ((fiberInclusion.obj y).left.structureHom.toShHom)
      (FlatSchemeCat.fiberResidueThickening Λ k Y hY y)
      (f.toShHom) (𝟙 _)
      (eqToHom (congrArg (fun A : ArtinianLocalAlgCat Λ k ↦
        (Spec (CommRingCat.of A.carrier)).toRingedSpace) (x.property.trans y.property.symm))) :=
  let ν := ((FlatSchemeCat.immersionKernelIsoUnit Λ k Y hY y).hom ≫
      SheafOfModules.unitToPushforwardObjUnit (toRingCatSheafHom (f.toShHom)) ≫
      ((f.toShHom) _*).map (FlatSchemeCat.immersionKernelIsoUnit Λ k X hX x).inv)
  let Cube : Prop := CommDiagram
      ((FlatSchemeCat.immersionOf Λ k X hX x).toShHom) (hX.toShHom)
      ((fiberInclusion.obj x).left.structureHom.toShHom)
      (FlatSchemeCat.fiberResidueThickening Λ k X hX x)
      ((FlatSchemeCat.immersionOf Λ k Y hY y).toShHom) (hY.toShHom)
      ((fiberInclusion.obj y).left.structureHom.toShHom)
      (FlatSchemeCat.fiberResidueThickening Λ k Y hY y)
      (f.toShHom) (𝟙 _)
      (eqToHom (congrArg (fun A : ArtinianLocalAlgCat Λ k ↦
        (Spec (CommRingCat.of A.carrier)).toRingedSpace) (x.property.trans y.property.symm)))
  let laws : Cube ∧ ∀ h : Cube, KernelSquare h ν := sorry
  RelativeDiagram.of laws.1 ν (laws.2 laws.1)

/-- Transport `mapObstruction` of a pair of deformations into `obstructionSpace`. -/
def obstructionOfFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k))
    (y : (FlatSchemeCat.deformationForget Λ k Y hY).Fiber (dualNumber Λ k)) :
    obstructionSpace f hY :=
  mapObstruction (pairRelativeDiagram Λ k f hX hY hf x y) ≫
    (shiftFunctor _ (1 : ℤ)).map
      ((DerivedCategory.Q.map
        ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).map
          ((FlatSchemeCat.immersionKernelIsoUnit Λ k X hX x).hom))))

/-- The connecting map `T Def_X × T Def_Y ⟶ Ext¹(Lf^* NL_{Y/k}, O_X)`. -/
def prodTangentToExt {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    (FlatSchemeCat.tangentSpace Λ k X hX × FlatSchemeCat.tangentSpace Λ k Y hY) →ₗ[k] obstructionSpace f hY :=
  let g := fun x y ↦ obstructionOfFiber Λ k f hX hY hf x y
  let Descent : Prop := ∀ x₁ x₂ y₁ y₂,
    Nonempty (x₁ ≅ x₂) → Nonempty (y₁ ≅ y₂) → g x₁ y₁ = g x₂ y₂
  let descend (h : Descent)
      (p : FlatSchemeCat.tangentSpace Λ k X hX × FlatSchemeCat.tangentSpace Λ k Y hY) :=
    Quotient.lift₂ g (fun x₁ y₁ x₂ y₂ hx hy ↦ h x₁ x₂ y₁ y₂ hx hy) p.1 p.2
  let laws : Descent ∧ ∀ h : Descent, IsLinearMap k (descend h) := sorry
  IsLinearMap.mk' (descend laws.1) (laws.2 laws.1)

/-- `prodTangentToExt` on represented classes is `obstructionOfFiber`. -/
theorem prodTangentToExt_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k))
    (y : (FlatSchemeCat.deformationForget Λ k Y hY).Fiber (dualNumber Λ k)) :
    prodTangentToExt Λ k f hX hY hf
        (Functor.tangentSpace.mk (FlatSchemeCat.deformationForget Λ k X hX) x,
          Functor.tangentSpace.mk (FlatSchemeCat.deformationForget Λ k Y hY) y) =
      obstructionOfFiber Λ k f hX hY hf x y := sorry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
variable (hf : f ≫ hY = hX)

/-- The infinitesimal automorphism forgetful map is injective. -/
theorem infToProdInf_injective :
    Function.Injective (infToProdInf Λ k f hX hY hf) := sorry

/-- The infinitesimal difference map has kernel equal to the image of compatible automorphisms. -/
theorem exact_inf_prodInf_der :
    Function.Exact (infToProdInf Λ k f hX hY hf)
      (prodInfToDer Λ k f hX hY hf) := sorry

/-- A derivation gives a trivial deformation exactly when it comes from an infinitesimal change of coordinates. -/
theorem exact_prodInf_der_tangent :
    Function.Exact (prodInfToDer Λ k f hX hY hf)
      (derToTangent Λ k f hX hY hf) := sorry

/-- A morphism deformation has trivial source and target classes exactly when induced by a derivation. -/
theorem exact_der_tangent_prodTangent :
    Function.Exact (derToTangent Λ k f hX hY hf)
      (tangentToProdTangent Λ k f hX hY hf) := sorry

/-- The obstruction to lifting a scheme morphism vanishes exactly on pairs induced by morphism deformations. -/
theorem exact_prodTangent_ext :
    Function.Exact (tangentToProdTangent Λ k f hX hY hf)
      (prodTangentToExt Λ k f hX hY hf) := sorry


end FlatSchemeMorphismCat
