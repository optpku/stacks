/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import stacks_project.Chap91.Lemma_91_7_1
public import stacks_project.Chap91.Lemma_91_7_1_Obstruction
public import stacks_project.Chap91.«91_7_0_1_Solution»
public import stacks_project.Chap93.Lemma_93_10_3_Deformation

/-!
# Connecting Hom and Ext maps of the morphism-deformation exact sequence

The middle arrows of Lemma 93.10.3 compare infinitesimal automorphisms with
`Hom(Ω_{Y/k}, f_* O_X)` and first-order lifts with the obstruction class in
`Ext¹(Lf^* NL_{Y/k}, O_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open Functor.Fiber
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Module.Associated
open AlgebraicGeometry.RingedSpace.Thickening
open ArtinianLocalAlgCat
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry DerivedExt DualNumber RingedSpaceDerivedPullback

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeMorphismCat

variable {Λ k}

/-- The ringed-space morphism associated with a morphism of schemes. -/
abbrev toRSHom {X Y : Scheme.{u}} (φ : X ⟶ Y) :
    X.toRingedSpace ⟶ Y.toRingedSpace :=
  φ.toLRSHom.toShHom

/-- The sheaf of relative differentials `Ω_{Y/k}`. -/
abbrev differentialsY (Y : Scheme.{u}) (hY : Y ⟶ Spec (CommRingCat.of k)) :
    Y.toRingedSpace.Modules :=
  RingedSpace.Hom.differentials (toRSHom hY)

/-- The pushforward `f_* O_X`. -/
abbrev pushforwardUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.toRingedSpace.Modules :=
  ((toRSHom f) _*).obj (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)

/-- Derivations `Der_k(O_Y, f_* O_X)`, realized as `Hom_{O_Y}(Ω_{Y/k}, f_* O_X)`. -/
abbrev derivations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) : Type u :=
  Ω[toRSHom hY] ⟶ pushforwardUnit f

/-- Unfolding of `derivations`. -/
theorem derivations_def {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) :
    derivations f hY = (differentialsY Y hY ⟶ pushforwardUnit f) := sorry

/-- The representing equivalence `Der_k(O_Y, f_* O_X) ≃ Hom(Ω_{Y/k}, f_* O_X)`. -/
def derEquivHomOmega {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) :
    RingedSpace.Hom.derivations (toRSHom hY) (pushforwardUnit f) ≃ derivations f hY :=
  (RingedSpace.Hom.homEquiv (toRSHom hY) (pushforwardUnit f)).symm

/-- `derEquivHomOmega` is the inverse of `homEquiv`. -/
theorem derEquivHomOmega_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k))
    (D : RingedSpace.Hom.derivations (toRSHom hY) (pushforwardUnit f)) :
    derEquivHomOmega f hY D =
      (RingedSpace.Hom.homEquiv (toRSHom hY) (pushforwardUnit f)).symm D := sorry

/-- Additive structure on `Hom(Ω_{Y/k}, f_* O_X)`. -/
instance instAddCommGroup_derivations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) : AddCommGroup (derivations f hY) :=
  inferInstance

/-- Scalar multiplication on `Hom(Ω_{Y/k}, f_* O_X)` by postcomposition with multiplication
by the global function induced by `c` through `hY`. -/
def smulDerivations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) (c : k) (α : derivations f hY) :
    derivations f hY :=
  α ≫ GlobalSections.mul (Scheme.Hom.globalSectionsMap hY c) (pushforwardUnit f)

/-- `k`-vector space structure on `Der_k(O_Y, f_* O_X)`. -/
instance instModule_derivations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) : Module k (derivations f hY) where
  smul := smulDerivations f hY
  one_smul := sorry
  zero_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  mul_smul := sorry

/-- The naive cotangent complex `NL_{Y/k}`. -/
abbrev naiveCotangentY {Y : Scheme.{u}} (hY : Y ⟶ Spec (CommRingCat.of k)) :
    CochainComplex Y.toRingedSpace.Modules ℤ :=
  NL[toRSHom hY]

/-- The obstruction space `Ext¹_{O_X}(Lf^* NL_{Y/k}, O_X)`. -/
abbrev obstructionSpace {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) : Type (u + 1) :=
  Ext⁽(1 : ℤ)⁾((modulePullbackDerived (toRSHom f)).obj
      (DerivedCategory.Q.obj (naiveCotangentY hY)),
    DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)))

/-- Unfolding of `obstructionSpace`. -/
theorem obstructionSpace_def {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) :
    obstructionSpace f hY =
      Ext⁽(1 : ℤ)⁾((modulePullbackDerived (toRSHom f)).obj
          (DerivedCategory.Q.obj (naiveCotangentY hY)),
        DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj
            (SheafOfModules.unit X.toRingedSpace.ringCatSheaf))) := sorry

/-- Additive structure on the obstruction space. -/
instance instAddCommGroup_obstructionSpace {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : Y ⟶ Spec (CommRingCat.of k)) : AddCommGroup (obstructionSpace f hY) :=
  inferInstance

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
    (hY : Y ⟶ Spec (CommRingCat.of k)) : Module k (obstructionSpace f hY) where
  smul := smulObstruction f hY
  one_smul := sorry
  zero_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  mul_smul := sorry

section DualNumberLifts

variable (Λ k)

/-- Closed immersion of `X` into the trivial dual-number thickening, as a morphism of
ringed spaces. -/
abbrev trivialSourceImmersionRS (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    X.toRingedSpace ⟶ (trivialSource Λ k X hX).toRingedSpace :=
  toRSHom (FlatSchemeCat.trivialSchemeImmersion Λ k X hX)

/-- Closed immersion of `Y` into the trivial dual-number thickening, as a morphism of
ringed spaces. -/
abbrev trivialTargetImmersionRS (Y : Scheme.{u})
    (hY : Y ⟶ Spec (CommRingCat.of k)) :
    Y.toRingedSpace ⟶ (trivialTarget Λ k Y hY).toRingedSpace :=
  toRSHom (FlatSchemeCat.trivialSchemeImmersion Λ k Y hY)

/-- First-order thickening of `Spec k` along `k ⟶ k[ε]`. -/
abbrev residueThickeningRS :
    (Spec (CommRingCat.of k)).toRingedSpace ⟶
      (Spec (CommRingCat.of (dualNumber Λ k).carrier)).toRingedSpace :=
  toRSHom (specMap (dualNumberToResidue Λ k))

/-- The trivial dual-number morphism as a morphism of ringed spaces. -/
abbrev trivialHomRS {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k)) :
    (trivialSource Λ k X hX).toRingedSpace ⟶ (trivialTarget Λ k Y hY).toRingedSpace :=
  toRSHom (trivialHom Λ k f hX hY)

/-- The source immersion of the trivial dual-number thickening is first-order. -/
instance instIsFirstOrderThickening_source (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    IsFirstOrderThickening
      (trivialSourceImmersionRS Λ k X hX :
        X.toRingedSpace ⟶ (trivialSource Λ k X hX).toRingedSpace) := sorry

/-- The target immersion of the trivial dual-number thickening is first-order. -/
instance instIsFirstOrderThickening_target (Y : Scheme.{u})
    (hY : Y ⟶ Spec (CommRingCat.of k)) :
    IsFirstOrderThickening
      (trivialTargetImmersionRS Λ k Y hY :
        Y.toRingedSpace ⟶ (trivialTarget Λ k Y hY).toRingedSpace) := sorry

/-- The dual-number thickening of `Spec k` is first-order. -/
instance instIsFirstOrderThickening_residue :
    IsFirstOrderThickening
      (residueThickeningRS Λ k :
        (Spec (CommRingCat.of k)).toRingedSpace ⟶
          (Spec (CommRingCat.of (dualNumber Λ k).carrier)).toRingedSpace) := sorry

/-- The commutative first-order cube of the trivial dual-number lift of `f`. -/
def trivialCommDiagram {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    CommDiagram
      (trivialSourceImmersionRS Λ k X hX) (toRSHom hX)
      (toRSHom (trivialSourceOver Λ k X hX)) (residueThickeningRS Λ k)
      (trivialTargetImmersionRS Λ k Y hY) (toRSHom hY)
      (toRSHom (trivialTargetOver Λ k Y hY)) (residueThickeningRS Λ k)
      (toRSHom f) (𝟙 _) (𝟙 _) :=
  CommDiagram.mk sorry sorry sorry sorry

/-- Canonical comparison of kernel ideals along `f` for the trivial dual-number cube. -/
def trivialKernelMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k)) :
    idealModule (trivialTargetImmersionRS Λ k Y hY) ⟶
      ((toRSHom f) _*).obj (idealModule (trivialSourceImmersionRS Λ k X hX)) :=
  kernelMapOf (trivialTargetImmersionRS Λ k Y hY) (toRSHom f)
    (trivialSourceImmersionRS Λ k X hX) inferInstance
    (trivialHomRS Λ k f hX hY) sorry

/-- The relative first-order diagram of the trivial dual-number lift of `f`. -/
def trivialRelativeDiagram {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    RelativeDiagram
      (trivialSourceImmersionRS Λ k X hX) (toRSHom hX)
      (toRSHom (trivialSourceOver Λ k X hX)) (residueThickeningRS Λ k)
      (trivialTargetImmersionRS Λ k Y hY) (toRSHom hY)
      (toRSHom (trivialTargetOver Λ k Y hY)) (residueThickeningRS Λ k)
      (toRSHom f) (𝟙 _) (𝟙 _) :=
  RelativeDiagram.of (trivialCommDiagram Λ k f hX hY hf)
    (trivialKernelMap Λ k f hX hY) sorry

/-- The trivial lift `f'` as a fitting map of `trivialRelativeDiagram`. -/
def trivialFittingMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    FittingMap (trivialRelativeDiagram Λ k f hX hY hf) :=
  FittingMap.of (trivialHomRS Λ k f hX hY) sorry sorry sorry

/-- The scheme automorphism of `X'` underlying an infinitesimal automorphism of `X`. -/
def sourceSchemeHom (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] (α : FlatSchemeCat.inf Λ k X hX) :
    trivialSource Λ k X hX ⟶ trivialSource Λ k X hX :=
  (fiberInclusion.map α.val.hom).schemeHom

/-- The inverse scheme automorphism of `Y'` underlying an infinitesimal automorphism of `Y`. -/
def targetSchemeInv (Y : Scheme.{u}) (hY : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hY] (β : FlatSchemeCat.inf Λ k Y hY) :
    trivialTarget Λ k Y hY ⟶ trivialTarget Λ k Y hY :=
  (fiberInclusion.map β.val.inv).schemeHom

/-- The conjugated morphism `β⁻¹ ∘ f' ∘ α` of trivial dual-number thickenings. -/
def conjugatedHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (p : prodInf Λ k f hX hY hf) :
    trivialSource Λ k X hX ⟶ trivialTarget Λ k Y hY :=
  sourceSchemeHom Λ k X hX p.1 ≫ trivialHom Λ k f hX hY ≫ targetSchemeInv Λ k Y hY p.2

/-- The conjugated morphism as a fitting map of the trivial dual-number cube. -/
def conjugatedFittingMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (p : prodInf Λ k f hX hY hf) :
    FittingMap (trivialRelativeDiagram Λ k f hX hY hf) :=
  FittingMap.of (toRSHom (conjugatedHom Λ k f hX hY hf p)) sorry sorry sorry

/-- The kernel of the coefficient projection `k[ε] ⟶ k`. -/
abbrev dualNumberKernel : Type u :=
  RingHom.ker (AlgHom.toRingHom (dualNumberToResidue Λ k).hom)

/-- Scalar multiplication on `ker(k[ε] ⟶ k)` through the residue field. -/
instance instModule_dualNumberKernel : Module k (dualNumberKernel Λ k) where
  smul r x := ⟨⟨x.1.fst, r * x.1.snd⟩, sorry⟩
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- ε-coefficient identification `ker(k[ε] ⟶ k) ≃ k`. -/
def dualNumberKernelEquiv : dualNumberKernel Λ k ≃ₗ[k] k where
  toFun x := x.1.snd
  invFun c := ⟨⟨0, c⟩, sorry⟩
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_smul' := sorry

/-- `dualNumberKernelEquiv` is the second projection on a kernel element. -/
theorem dualNumberKernelEquiv_apply (x : dualNumberKernel Λ k) :
    dualNumberKernelEquiv Λ k x = x.1.snd := sorry

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
    idealModule (residueThickeningRS Λ k) ⟶
      ((toRSHom hX) _*).obj (idealModule (trivialSourceImmersionRS Λ k X hX)) :=
  kernelMapOf (residueThickeningRS Λ k) (toRSHom hX)
    (trivialSourceImmersionRS Λ k X hX) inferInstance
    (toRSHom (trivialSourceOver Λ k X hX)) sorry

/-- Adjunct `hX^* Ker(Spec k → Spec k[ε]) ⟶ Ker(X → X')` of `structureKernelMap`. -/
def structureKernelPull (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    ((toRSHom hX) ^*).obj (idealModule (residueThickeningRS Λ k)) ⟶
      idealModule (trivialSourceImmersionRS Λ k X hX) :=
  cPull (residueThickeningRS Λ k) (toRSHom hX) (structureKernelMap Λ k X hX)

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

/-- Comparison `Ker(Spec k → Spec k[ε]) ⟶ O_{Spec k}` obtained by pulling back the
kernel-ideal inclusion along the dual-number thickening. -/
def residueKernelToUnit :
    idealModule (residueThickeningRS Λ k) ⟶
      SheafOfModules.unit (Spec (CommRingCat.of k)).toRingedSpace.ringCatSheaf :=
  ((residueThickeningRS Λ k) ^*).map (kernelIdealι (residueThickeningRS Λ k)) ≫
    ((residueThickeningRS Λ k) ^*).map
      (unitIsoTensorUnit
        (Spec (CommRingCat.of (dualNumber Λ k).carrier)).toRingedSpace).hom ≫
    (pullbackUnitIso (residueThickeningRS Λ k)).hom ≫
    (unitIsoTensorUnit (Spec (CommRingCat.of k)).toRingedSpace).inv

/-- The comparison `Ker(Spec k → Spec k[ε]) ⟶ O_{Spec k}` is an isomorphism. -/
instance instIsIso_residueKernelToUnit : IsIso (residueKernelToUnit Λ k) := sorry

/-- Identification `Ker(Spec k → Spec k[ε]) ≅ Associated(ker)` on `Spec k`, not a sheaf
equality. -/
def residueKernelIsoAssociated :
    idealModule (residueThickeningRS Λ k) ≅ residueAssociatedKernel Λ k where
  hom := residueKernelToUnit Λ k ≫ (residueAssociatedIsoUnit Λ k).inv
  inv := (residueAssociatedIsoUnit Λ k).hom ≫ inv (residueKernelToUnit Λ k)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identification `Ker(Spec k → Spec k[ε]) ≅ O_{Spec k}` via ε-coefficients. -/
def residueKernelIsoUnit :
    idealModule (residueThickeningRS Λ k) ≅
      SheafOfModules.unit (Spec (CommRingCat.of k)).toRingedSpace.ringCatSheaf :=
  residueKernelIsoAssociated Λ k ≪≫ residueAssociatedIsoUnit Λ k

/-- Pullback of `Associated_{Spec k}(ker)` along `hX` is `Associated_X(ker)`. -/
def associatedKernelPullbackIso (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    ((toRSHom hX) ^*).obj (residueAssociatedKernel Λ k) ≅
      associatedDualNumberKernel Λ k X hX :=
  obj.pullbackIso (toRSHom hX)
    (Scheme.Hom.globalSectionsMap (𝟙 (Spec (CommRingCat.of k))))
    (ModuleCat.of k (dualNumberKernel Λ k))

/-- Identification of the kernel of the trivial source thickening with `O_X`,
obtained by composing `structureKernelPull` with the ε-coefficient iso
`ker(k[ε] ⟶ k) ≃ k` and the associated-sheaf unit. -/
def sourceKernelIsoUnit (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    idealModule (trivialSourceImmersionRS Λ k X hX) ≅
      SheafOfModules.unit X.toRingedSpace.ringCatSheaf :=
  (asIso (structureKernelPull Λ k X hX)).symm ≪≫
    ((toRSHom hX) ^*).mapIso (residueKernelIsoAssociated Λ k) ≪≫
    associatedKernelPullbackIso Λ k X hX ≪≫
    associatedKernelIsoUnit Λ k X hX

/-- Forward map of `sourceKernelIsoUnit`. -/
def sourceKernelIsoUnit_hom (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    idealModule (trivialSourceImmersionRS Λ k X hX) ⟶
      SheafOfModules.unit X.toRingedSpace.ringCatSheaf :=
  (sourceKernelIsoUnit Λ k X hX).hom

/-- Inverse map of `sourceKernelIsoUnit`. -/
def sourceKernelIsoUnit_inv (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    SheafOfModules.unit X.toRingedSpace.ringCatSheaf ⟶
      idealModule (trivialSourceImmersionRS Λ k X hX) :=
  (sourceKernelIsoUnit Λ k X hX).inv

/-- `sourceKernelIsoUnit` identifies `Ker(X → X')` with `O_X`. -/
theorem sourceKernelIsoUnit_spec (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    (sourceKernelIsoUnit Λ k X hX).hom ≫ (sourceKernelIsoUnit Λ k X hX).inv =
      𝟙 (idealModule (trivialSourceImmersionRS Λ k X hX)) ∧
    (sourceKernelIsoUnit Λ k X hX).inv ≫ (sourceKernelIsoUnit Λ k X hX).hom =
      𝟙 (SheafOfModules.unit X.toRingedSpace.ringCatSheaf) := sorry

/-- Transport `Hom(Ω_{Y/k}, f_* Ker(X → X'))` to `Hom(Ω_{Y/k}, f_* O_X)`. -/
def homKernelToDerivations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (α : differentialsY Y hY ⟶
      ((toRSHom f) _*).obj (idealModule (trivialSourceImmersionRS Λ k X hX))) :
    derivations f hY :=
  α ≫ ((toRSHom f) _*).map (sourceKernelIsoUnit Λ k X hX).hom

/-- Transport a derivation into a kernel-valued Hom via `sourceKernelIsoUnit.inv`. -/
def derivationsToHomKernel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (α : derivations f hY) :
    differentialsY Y hY ⟶ ((toRSHom f) _*).obj (idealModule (trivialSourceImmersionRS Λ k X hX)) :=
  α ≫ ((toRSHom f) _*).map (sourceKernelIsoUnit Λ k X hX).inv

/-- The connecting map `Inf(Def_X) × Inf(Def_Y) ⟶ Der_k(O_Y, f_* O_X)` sending
`(α, β)` to the 91.7.1 difference of `f'` and `β⁻¹ ∘ f' ∘ α`. -/
def prodInfToDer {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    prodInf Λ k f hX hY hf →ₗ[k] derivations f hY where
  toFun p :=
    homKernelToDerivations Λ k f hX hY
      (FittingMap.diff (trivialFittingMap Λ k f hX hY hf)
        (conjugatedFittingMap Λ k f hX hY hf p))
  map_add' := sorry
  map_smul' := sorry

/-- `prodInfToDer` is the 91.7.1 difference of `f'` and the conjugated morphism. -/
theorem prodInfToDer_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (p : prodInf Λ k f hX hY hf) :
    prodInfToDer Λ k f hX hY hf p =
      homKernelToDerivations Λ k f hX hY
        (FittingMap.diff (trivialFittingMap Λ k f hX hY hf)
          (conjugatedFittingMap Λ k f hX hY hf p)) := sorry

/-- The locally ringed space morphism obtained by perturbing `f'` by a derivation. -/
def perturbedLRSHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (α : derivations f hY) :
    (trivialSource Λ k X hX).toLocallyRingedSpace ⟶
      (trivialTarget Λ k Y hY).toLocallyRingedSpace :=
  LocallyRingedSpace.homMk
    (FittingMap.perturb (derivationsToHomKernel Λ k f hX hY α)
      (trivialFittingMap Λ k f hX hY hf)).hom sorry

/-- The scheme morphism `X' ⟶ Y'` underlying a perturbed fitting map. -/
def perturbedSchemeHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (α : derivations f hY) :
    trivialSource Λ k X hX ⟶ trivialTarget Λ k Y hY :=
  Scheme.Hom.mk (perturbedLRSHom Λ k f hX hY hf α)

/-- Dual-number object of `FlatSchemeMorphismCat` obtained by perturbing `f'` by a derivation. -/
def perturbedObj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (α : derivations f hY) : FlatSchemeMorphismCat Λ k :=
  of (dualNumber Λ k) (trivialSource Λ k X hX) (trivialTarget Λ k Y hY)
    (perturbedSchemeHom Λ k f hX hY hf α)
    (trivialSourceOver Λ k X hX) (trivialTargetOver Λ k Y hY) sorry

/-- The slice arrow of a derivation-perturbed lift toward the residue object. -/
def perturbedLiftHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (α : derivations f hY) :
    perturbedObj Λ k f hX hY hf α ⟶
      fiberInclusion.obj (residueObj Λ k X Y f hX hY hf) :=
  Hom.of (dualNumberToResidue Λ k)
    (FlatSchemeCat.trivialSchemeImmersion Λ k X hX)
    (FlatSchemeCat.trivialSchemeImmersion Λ k Y hY) sorry sorry

/-- The slice object of a derivation-perturbed lift. -/
def perturbedLift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
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
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    derivations f hY →ₗ[k] tangentSpace Λ k f hX hY hf where
  toFun α := tangentSpaceMk Λ k f hX hY hf (perturbedLift Λ k f hX hY hf α)
  map_add' := sorry
  map_smul' := sorry

/-- `derToTangent` sends a derivation to the class of the corresponding perturbed lift. -/
theorem derToTangent_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (α : derivations f hY) :
    derToTangent Λ k f hX hY hf α =
      tangentSpaceMk Λ k f hX hY hf (perturbedLift Λ k f hX hY hf α) := sorry

/-- Closed immersion of `X` into a dual-number deformation of `X`. -/
def sourceImmersionOf (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    X ⟶ (fiberInclusion.obj x).left.scheme :=
  (fiberInclusion.obj x).hom.schemeHom

/-- Closed immersion of `Y` into a dual-number deformation of `Y`. -/
def targetImmersionOf (Y : Scheme.{u}) (hY : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hY]
    (y : (FlatSchemeCat.deformationForget Λ k Y hY).Fiber (dualNumber Λ k)) :
    Y ⟶ (fiberInclusion.obj y).left.scheme :=
  (fiberInclusion.obj y).hom.schemeHom

/-- A source dual-number immersion is a first-order thickening. -/
instance instIsFirstOrderThickening_sourceImmersionOf (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    IsFirstOrderThickening (toRSHom (sourceImmersionOf Λ k X hX x)) := sorry

/-- A target dual-number immersion is a first-order thickening. -/
instance instIsFirstOrderThickening_targetImmersionOf (Y : Scheme.{u})
    (hY : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hY]
    (y : (FlatSchemeCat.deformationForget Λ k Y hY).Fiber (dualNumber Λ k)) :
    IsFirstOrderThickening (toRSHom (targetImmersionOf Λ k Y hY y)) := sorry

/-- Dual-number thickening of `Spec k` with codomain the spectrum of a fibre object's base. -/
def fiberResidueThickening (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    (Spec (CommRingCat.of k)).toRingedSpace ⟶
      (Spec (CommRingCat.of (fiberInclusion.obj x).left.base.carrier)).toRingedSpace :=
  residueThickeningRS Λ k ≫
    eqToHom
      (congrArg (fun A : ArtinianLocalAlgCat Λ k ↦
          (Spec (CommRingCat.of A.carrier)).toRingedSpace)
        (x.property.symm.trans
          (rfl : (FlatSchemeCat.deformationForget Λ k X hX).obj (fiberInclusion.obj x) =
            (fiberInclusion.obj x).left.base)))

/-- Dual-number thickenings of `Spec k` attached to fibre objects are first-order. -/
instance instIsFirstOrderThickening_fiberResidueThickening
    (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    IsFirstOrderThickening (fiberResidueThickening Λ k X hX x) := sorry

/-- Comparison `Ker(Spec k → Spec k[ε]) ⟶ hX_* Ker(X → X_ε)` of a dual-number fibre. -/
def fiberStructureKernelMap (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    idealModule (fiberResidueThickening Λ k X hX x) ⟶
      ((toRSHom hX) _*).obj (idealModule (toRSHom (sourceImmersionOf Λ k X hX x))) :=
  kernelMapOf (fiberResidueThickening Λ k X hX x) (toRSHom hX)
    (toRSHom (sourceImmersionOf Λ k X hX x)) inferInstance
    (toRSHom (fiberInclusion.obj x).left.structureHom) sorry

/-- Adjunct of `fiberStructureKernelMap`. -/
def fiberStructureKernelPull (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    ((toRSHom hX) ^*).obj (idealModule (fiberResidueThickening Λ k X hX x)) ⟶
      idealModule (toRSHom (sourceImmersionOf Λ k X hX x)) :=
  cPull (fiberResidueThickening Λ k X hX x) (toRSHom hX)
    (fiberStructureKernelMap Λ k X hX x)

/-- The fibrewise structure-square kernel comparison is an isomorphism. -/
instance instIsIso_fiberStructureKernelPull (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    IsIso (fiberStructureKernelPull Λ k X hX x) := sorry

/-- Comparison of kernel ideals along the fibre base identification
`fiberResidueThickening = residueThickening ≫ eqToHom`. -/
def fiberResidueKernelIso (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    idealModule (fiberResidueThickening Λ k X hX x) ≅
      idealModule (residueThickeningRS Λ k) where
  hom :=
    idealMap
      (eqToHom
        (congrArg (fun A : ArtinianLocalAlgCat Λ k ↦
            (Spec (CommRingCat.of A.carrier)).toRingedSpace)
          (x.property.symm.trans
            (rfl : (FlatSchemeCat.deformationForget Λ k X hX).obj
                (fiberInclusion.obj x) =
              (fiberInclusion.obj x).left.base))))
      rfl
  inv :=
    idealMap
      (eqToHom
        (congrArg (fun A : ArtinianLocalAlgCat Λ k ↦
            (Spec (CommRingCat.of A.carrier)).toRingedSpace)
          ((rfl : (FlatSchemeCat.deformationForget Λ k X hX).obj
                (fiberInclusion.obj x) =
              (fiberInclusion.obj x).left.base).symm.trans x.property)))
      sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identification of the kernel of a source dual-number thickening with `O_X`,
obtained by composing `fiberStructureKernelPull` with the ε-coefficient iso
`ker(k[ε] ⟶ k) ≃ k` and the associated-sheaf unit. -/
def sourceImmersionKernelIsoUnit (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    idealModule (toRSHom (sourceImmersionOf Λ k X hX x)) ≅
      SheafOfModules.unit X.toRingedSpace.ringCatSheaf :=
  (asIso (fiberStructureKernelPull Λ k X hX x)).symm ≪≫
    ((toRSHom hX) ^*).mapIso (fiberResidueKernelIso Λ k X hX x) ≪≫
    ((toRSHom hX) ^*).mapIso (residueKernelIsoAssociated Λ k) ≪≫
    associatedKernelPullbackIso Λ k X hX ≪≫
    associatedKernelIsoUnit Λ k X hX

/-- Forward map of `sourceImmersionKernelIsoUnit`. -/
def sourceImmersionKernelIsoUnit_hom (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    idealModule (toRSHom (sourceImmersionOf Λ k X hX x)) ⟶
      SheafOfModules.unit X.toRingedSpace.ringCatSheaf :=
  (sourceImmersionKernelIsoUnit Λ k X hX x).hom

/-- Inverse map of `sourceImmersionKernelIsoUnit`. -/
def sourceImmersionKernelIsoUnit_inv (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    SheafOfModules.unit X.toRingedSpace.ringCatSheaf ⟶
      idealModule (toRSHom (sourceImmersionOf Λ k X hX x)) :=
  (sourceImmersionKernelIsoUnit Λ k X hX x).inv

/-- `sourceImmersionKernelIsoUnit` identifies `Ker(X → X_ε)` with `O_X`. -/
theorem sourceImmersionKernelIsoUnit_spec (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    (sourceImmersionKernelIsoUnit Λ k X hX x).hom ≫
        (sourceImmersionKernelIsoUnit Λ k X hX x).inv =
      𝟙 (idealModule (toRSHom (sourceImmersionOf Λ k X hX x))) ∧
    (sourceImmersionKernelIsoUnit Λ k X hX x).inv ≫
        (sourceImmersionKernelIsoUnit Λ k X hX x).hom =
      𝟙 (SheafOfModules.unit X.toRingedSpace.ringCatSheaf) := sorry

/-- Relative first-order diagram comparing deformations `X_ε` and `Y_ε` of `X` and `Y`. -/
def pairRelativeDiagram {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k))
    (y : (FlatSchemeCat.deformationForget Λ k Y hY).Fiber (dualNumber Λ k)) :
    RelativeDiagram
      (toRSHom (sourceImmersionOf Λ k X hX x)) (toRSHom hX)
      (toRSHom (fiberInclusion.obj x).left.structureHom)
      (fiberResidueThickening Λ k X hX x)
      (toRSHom (targetImmersionOf Λ k Y hY y)) (toRSHom hY)
      (toRSHom (fiberInclusion.obj y).left.structureHom)
      (fiberResidueThickening Λ k Y hY y)
      (toRSHom f) (𝟙 _)
      (eqToHom
        (congrArg (fun A : ArtinianLocalAlgCat Λ k ↦
            (Spec (CommRingCat.of A.carrier)).toRingedSpace)
          ((rfl : (FlatSchemeCat.deformationForget Λ k X hX).obj (fiberInclusion.obj x) =
              (fiberInclusion.obj x).left.base).symm.trans
            (x.property.trans
              (y.property.symm.trans
                (rfl : (FlatSchemeCat.deformationForget Λ k Y hY).obj (fiberInclusion.obj y) =
                  (fiberInclusion.obj y).left.base)))))) :=
  RelativeDiagram.of (CommDiagram.mk sorry sorry sorry sorry)
    ((sourceImmersionKernelIsoUnit Λ k Y hY y).hom ≫
      SheafOfModules.unitToPushforwardObjUnit (toRingCatSheafHom (toRSHom f)) ≫
      ((toRSHom f) _*).map (sourceImmersionKernelIsoUnit Λ k X hX x).inv) sorry

/-- Transport `mapObstruction` of a pair of deformations into `obstructionSpace`. -/
def obstructionOfFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k))
    (y : (FlatSchemeCat.deformationForget Λ k Y hY).Fiber (dualNumber Λ k)) :
    obstructionSpace f hY :=
  mapObstruction (pairRelativeDiagram Λ k f hX hY hf x y) ≫
    (shiftFunctor _ (1 : ℤ)).map
      ((DerivedCategory.Q.map
        ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).map
          ((sourceImmersionKernelIsoUnit Λ k X hX x).hom))))

/-- The connecting map `T Def_X × T Def_Y ⟶ Ext¹(Lf^* NL_{Y/k}, O_X)`. -/
def prodTangentToExt {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    prodTangent Λ k f hX hY hf →ₗ[k] obstructionSpace f hY where
  toFun p :=
    Quotient.lift₂
      (fun x y ↦ obstructionOfFiber Λ k f hX hY hf x y)
      (fun _ _ _ _ _ _ ↦ sorry)
      p.1 p.2
  map_add' := sorry
  map_smul' := sorry

/-- `prodTangentToExt` on represented classes is `obstructionOfFiber`. -/
theorem prodTangentToExt_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (x : (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k))
    (y : (FlatSchemeCat.deformationForget Λ k Y hY).Fiber (dualNumber Λ k)) :
    prodTangentToExt Λ k f hX hY hf
        (FlatSchemeCat.tangentSpaceMk Λ k X hX x,
          FlatSchemeCat.tangentSpaceMk Λ k Y hY y) =
      obstructionOfFiber Λ k f hX hY hf x y := sorry

end DualNumberLifts

end FlatSchemeMorphismCat
