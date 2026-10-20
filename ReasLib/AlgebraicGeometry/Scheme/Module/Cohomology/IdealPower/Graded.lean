module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Product
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Rees
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module.LocalFiniteType
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Graded higher direct images of ideal-power products

The graded `𝒪_Y`-module sheaf
`M = ⨁_{n ≥ 0} R^p f_*(I^n F)` over the Rees algebra `A = ⨁_{n ≥ 0} I^n`,
together with the homogeneous action maps
`I^n ⊗ R^p f_*(I^m F) ⟶ R^p f_*(I^{n+m} F)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace.Hom
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace IdealPowerCohomology

variable {Y : Scheme.{u}}

/-- The sheaf `I^n F` on `X`, realized as the image of the action of `(I.comap f)^n`. -/
noncomputable abbrev product (I : Y.IdealSheafData) {X : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (n : ℕ) : X.Modules :=
  (idealPowerProductSubobject (I.comap f) F n : X.Modules)


/-- The higher direct image `R^p f_*(I^n F)`, as a module sheaf on `Y`. -/
noncomputable abbrev piece (I : Y.IdealSheafData) {X : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (p n : ℕ) : Y.Modules :=
  Scheme.Modules.fromRingedSpaceObj Y
    (higherDirectImageModule f.toShHom
      (Scheme.Modules.toRingedSpaceObj X (product I f F n)) p)


/-- The zero module sheaf on `Y`, used for negative graded pieces. -/
noncomputable abbrev zeroModule : Y.Modules :=
  Scheme.Modules.fromRingedSpaceObj Y (⊥ : Y.IdealSheafData).toModule

/-- The image of `(I.comap f)^n ⊗ I^m F → I^m F` factors through `I^{n+m} F`. -/
theorem productAction_factors (I : Y.IdealSheafData) {X : Scheme.{u}}
    (f : X ⟶ Y) (F : X.Modules) (n m : ℕ) :
    (idealPowerProductSubobject (I.comap f) F (n + m)).Factors
      (IdealSheaf.action ((I.comap f) ^ n).toSubobject (product I f F m) ≫
        (idealPowerProductSubobject (I.comap f) F m).arrow) :=
  sorry

/-- Multiplication `(I.comap f)^n ⊗ I^m F ⟶ I^{n+m} F` on `X`. -/
noncomputable def productAction (I : Y.IdealSheafData) {X : Scheme.{u}}
    (f : X ⟶ Y) (F : X.Modules) (n m : ℕ) :
    (((I.comap f) ^ n).toModule ⊗ product I f F m : X.Modules) ⟶
      product I f F (n + m) :=
  (idealPowerProductSubobject (I.comap f) F (n + m)).factorThru
    (IdealSheaf.action ((I.comap f) ^ n).toSubobject (product I f F m) ≫
      (idealPowerProductSubobject (I.comap f) F m).arrow)
    (productAction_factors I f F n m)


/-- Higher direct image of `productAction`, as a morphism
`R^p f_*(((I.comap f)^n) ⊗ I^m F) ⟶ R^p f_*(I^{n+m} F)`. -/
noncomputable def productActionDirectImage (I : Y.IdealSheafData)
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p n m : ℕ) :
    Scheme.Modules.fromRingedSpaceObj Y
        (higherDirectImageModule f.toShHom
          (Scheme.Modules.toRingedSpaceObj X
            (((I.comap f) ^ n).toModule ⊗ product I f F m)) p) ⟶
      piece I f F p (n + m) :=
  Scheme.Modules.fromRingedSpaceMap Y
    (higherDirectImageModuleMap f.toShHom
      (Scheme.Modules.toRingedSpaceMap X (productAction I f F n m)) p)


/-- The inclusion of `(I.comap f)^n` into the structure module on `X`. -/
noncomputable def comapPowerArrow (I : Y.IdealSheafData) {X : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    Scheme.Modules.fromRingedSpaceObj X ((I.comap f) ^ n).toModule ⟶
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  Scheme.Modules.fromRingedSpaceMap X ((I.comap f) ^ n).toSubobject.arrow

/-- Pullback of the inclusion `I^n ⟶ 𝒪_Y`, identified with a morphism into `𝒪_X`. -/
noncomputable def pullbackReesArrow (I : Y.IdealSheafData) {X : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (IdealSheafData.reesAlgebraObj I n) ⟶
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  (Scheme.Modules.pullback f).map (IdealSheafData.reesArrow I n) ≫
    (Scheme.Modules.pullbackStructureSheafIso f).hom


/-- The image of the pulled-back inclusion of `I^n` factors through `(I.comap f)^n`. -/
theorem pullbackIdealPower_factors (I : Y.IdealSheafData) {X : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ((I.comap f) ^ n).toSubobject.Factors
      (Scheme.Modules.toRingedSpaceMap X (pullbackReesArrow I f n)) :=
  sorry

/-- Comparison `f^*(I^n) ⟶ (I.comap f)^n` of ideal-power pullbacks. -/
noncomputable def pullbackIdealPower (I : Y.IdealSheafData) {X : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (IdealSheafData.reesAlgebraObj I n) ⟶
      Scheme.Modules.fromRingedSpaceObj X ((I.comap f) ^ n).toModule :=
  Scheme.Modules.fromRingedSpaceMap X
    (((I.comap f) ^ n).toSubobject.factorThru
      (Scheme.Modules.toRingedSpaceMap X (pullbackReesArrow I f n))
      (pullbackIdealPower_factors I f n))

/-- Restriction square of `f` along an open of `Y`. -/
theorem restriction_commSq {X : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    CommSq (f ⁻¹ᵁ U).ι.toShHom (f ∣_ U).toShHom f.toShHom U.ι.toShHom :=
  ⟨((rfl :
        ((f ⁻¹ᵁ U).ι ≫ f).toShHom = (f ⁻¹ᵁ U).ι.toShHom ≫ f.toShHom).symm.trans
      ((congrArg (fun φ : (f ⁻¹ᵁ U).toScheme ⟶ Y ↦ φ.toShHom)
          (morphismRestrict_ι f U).symm).trans
        (rfl : ((f ∣_ U) ≫ U.ι).toShHom = (f ∣_ U).toShHom ≫ U.ι.toShHom)))⟩

/-- Restriction of higher direct images along an open of the target is invertible. -/
theorem restriction_baseChange_isIso {X : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (G : X.toRingedSpace.Modules) (p : ℕ) :
    IsIso (higherDirectImageModuleBaseChangeMap (restriction_commSq f U) G p) :=
  sorry

/-- A local section of `I^n` on `U`, as a global section of the restriction to `U`. -/
noncomputable def restrictReesSection (I : Y.IdealSheafData) (n : ℕ) (U : Y.Opens)
    (a : (IdealSheafData.reesAlgebraObj I n).val.obj (Opposite.op U)) :
    ((IdealSheafData.reesAlgebraObj I n).restrict U.ι).val.obj
      (Opposite.op (⊤ : Opens U.toScheme)) :=
  ((IdealSheafData.reesAlgebraObj I n).val.map
      (eqToHom (congrArg Opposite.op (Scheme.Opens.ι_image_top U).symm))).hom a

/-- The ringed-space morphism `𝟙 ⟶ I^n|_U` classified by a local section of `I^n`. -/
noncomputable def restrictReesTopHom (I : Y.IdealSheafData) (n : ℕ) (U : Y.Opens)
    (a : (IdealSheafData.reesAlgebraObj I n).val.obj (Opposite.op U)) :
    (𝟙_ U.toScheme.toRingedSpace.Modules) ⟶
      Scheme.Modules.toRingedSpaceObj U.toScheme
        ((IdealSheafData.reesAlgebraObj I n).restrict U.ι) :=
  RingedSpace.tensorUnitToUnitModule U.toScheme.toRingedSpace ≫
    RingedSpace.topSectionMorphism
      (Scheme.Modules.toRingedSpaceObj U.toScheme
        ((IdealSheafData.reesAlgebraObj I n).restrict U.ι))
      (restrictReesSection I n U a)

/-- The scheme-module morphism `𝟙 ⟶ I^n|_U` classified by a local section of `I^n`. -/
noncomputable def restrictReesUnitHom (I : Y.IdealSheafData) (n : ℕ) (U : Y.Opens)
    (a : (IdealSheafData.reesAlgebraObj I n).val.obj (Opposite.op U)) :
    (𝟙_ U.toScheme.Modules) ⟶ (IdealSheafData.reesAlgebraObj I n).restrict U.ι :=
  Scheme.Modules.fromRingedSpaceMap U.toScheme (restrictReesTopHom I n U a)

/-- The morphism `𝒪 ⟶ (I.comap f)^n` on `f⁻¹U` classified by the pullback of a local
section of `I^n`. -/
noncomputable def pullbackSectionUnitHom (I : Y.IdealSheafData)
    {X : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) (U : Y.Opens)
    (a : (IdealSheafData.reesAlgebraObj I n).val.obj (Opposite.op U)) :
    (𝟙_ ((f ⁻¹ᵁ U).toScheme.Modules)) ⟶
      (Scheme.Modules.fromRingedSpaceObj X ((I.comap f) ^ n).toModule).restrict
        (f ⁻¹ᵁ U).ι :=
  (Scheme.Modules.pullbackUnitIso (f ∣_ U)).inv ≫
    (Scheme.Modules.pullback (f ∣_ U)).map (restrictReesUnitHom I n U a) ≫
    (Scheme.Modules.pullbackRestrictIso f U (IdealSheafData.reesAlgebraObj I n)).hom ≫
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (pullbackIdealPower I f n)

/-- Tensor a restricted product with the pullback of a local section of `I^n`. -/
noncomputable def tensorByLocalSection (I : Y.IdealSheafData)
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (n m : ℕ) (U : Y.Opens)
    (a : (IdealSheafData.reesAlgebraObj I n).val.obj (Opposite.op U)) :
    (product I f F m).restrict (f ⁻¹ᵁ U).ι ⟶
      ((Scheme.Modules.fromRingedSpaceObj X ((I.comap f) ^ n).toModule ⊗
          product I f F m : X.Modules).restrict (f ⁻¹ᵁ U).ι) :=
  let A := Scheme.Modules.fromRingedSpaceObj X ((I.comap f) ^ n).toModule
  (λ_ ((product I f F m).restrict (f ⁻¹ᵁ U).ι)).inv ≫
    tensorHom (pullbackSectionUnitHom I f n U a) (𝟙 ((product I f F m).restrict (f ⁻¹ᵁ U).ι)) ≫
      (tensorHom
          ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).hom.app A)
          ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).hom.app
            (product I f F m)) ≫
        (Scheme.Modules.pullbackTensorIso (f ⁻¹ᵁ U).ι A (product I f F m)).inv ≫
          (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).inv.app
            (A ⊗ product I f F m))

/-- Identify a section of a module sheaf on `U` with a global section of its restriction. -/
noncomputable def restrictOpenSection {Y : Scheme.{u}} (M : Y.Modules) (U : Y.Opens)
    (x : M.val.obj (Opposite.op U)) :
    (M.restrict U.ι).val.obj (Opposite.op (⊤ : Opens U.toScheme)) :=
  (M.val.map
      (eqToHom (congrArg Opposite.op (Scheme.Opens.ι_image_top U).symm))).hom x

/-- Recover a section of a module sheaf on `U` from a global section of its restriction. -/
noncomputable def unrestrictOpenSection {Y : Scheme.{u}} (M : Y.Modules) (U : Y.Opens)
    (x : (M.restrict U.ι).val.obj (Opposite.op (⊤ : Opens U.toScheme))) :
    M.val.obj (Opposite.op U) :=
  (M.val.map
      (eqToHom (congrArg Opposite.op (Scheme.Opens.ι_image_top U)))).hom x

/-- Identify a section of `R^p f_*(I^n F)` on `U` with a global section of its restriction. -/
noncomputable def restrictPieceSection (I : Y.IdealSheafData)
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p n : ℕ) (U : Y.Opens)
    (x : (piece I f F p n).val.obj (Opposite.op U)) :
    ((piece I f F p n).restrict U.ι).val.obj (Opposite.op (⊤ : Opens U.toScheme)) :=
  restrictOpenSection (piece I f F p n) U x


/-- The sheaf `(I.comap f)^n ⊗ I^m F` on `X`. -/
noncomputable abbrev tensorProductModule (I : Y.IdealSheafData) {X : Scheme.{u}}
    (f : X ⟶ Y) (F : X.Modules) (n m : ℕ) : X.Modules :=
  Scheme.Modules.fromRingedSpaceObj X ((I.comap f) ^ n).toModule ⊗ product I f F m

/-- The higher direct image `R^p f_*(((I.comap f)^n) ⊗ I^m F)`. -/
noncomputable abbrev tensorPiece (I : Y.IdealSheafData) {X : Scheme.{u}}
    (f : X ⟶ Y) (F : X.Modules) (p n m : ℕ) : Y.Modules :=
  Scheme.Modules.fromRingedSpaceObj Y
    (higherDirectImageModule f.toShHom
      (Scheme.Modules.toRingedSpaceObj X (tensorProductModule I f F n m)) p)

/-- Local multiplication by a section of `I^n`, as a map of pullbacks to `f⁻¹U`. -/
noncomputable def tensorByLocalSectionPullback (I : Y.IdealSheafData)
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (n m : ℕ) (U : Y.Opens)
    (a : (IdealSheafData.reesAlgebraObj I n).val.obj (Opposite.op U)) :
    (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (product I f F m) ⟶
      (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (tensorProductModule I f F n m) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).inv.app (product I f F m) ≫
    tensorByLocalSection I f F n m U a ≫
    (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).hom.app
      (tensorProductModule I f F n m)

/-- Canonical comparison `I^n ⊗ R^p f_*(I^m F) ⟶ R^p f_*(((I.comap f)^n) ⊗ I^m F)`
on local sections, obtained by pulling the `I^n`-factor back to `X` and applying
functoriality of `R^p f_*` after restriction to the preimage. -/
noncomputable def tensorHigherDirectImageSection (I : Y.IdealSheafData)
    [I.toModule.IsQuasicoherent] {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (p n m : ℕ) (U : (Opens Y)ᵒᵖ)
    (a : ((IdealSheafData.reesAlgebra I).obj (Int.ofNat n)).val.obj U)
    (x : (piece I f F p m).val.obj U) :
    (tensorPiece I f F p n m).val.obj U :=
  let UY := U.unop
  let xPull :=
    (((Scheme.Modules.restrictFunctorIsoPullback UY.ι).hom.app
        (piece I f F p m)).val.app
      (Opposite.op (⊤ : Opens UY.toScheme))).hom
      (restrictPieceSection I f F p m UY x)
  let bc := higherDirectImageModuleBaseChangeMap (restriction_commSq f UY)
      (Scheme.Modules.toRingedSpaceObj X (product I f F m)) p
  let bc' := higherDirectImageModuleBaseChangeMap (restriction_commSq f UY)
      (Scheme.Modules.toRingedSpaceObj X (tensorProductModule I f F n m)) p
  let φ := tensorByLocalSectionPullback I f F n m UY a
  unrestrictOpenSection (tensorPiece I f F p n m) UY
    ((((Scheme.Modules.restrictFunctorIsoPullback UY.ι).inv.app
          (tensorPiece I f F p n m)).val.app
        (Opposite.op (⊤ : Opens UY.toScheme))).hom
      (((Scheme.Modules.fromRingedSpaceMap UY.toScheme
            (@CategoryTheory.inv _ _ _ _ bc'
              (restriction_baseChange_isIso f UY
                (Scheme.Modules.toRingedSpaceObj X (tensorProductModule I f F n m))
                p))).val.app
          (Opposite.op (⊤ : Opens UY.toScheme))).hom
        (((higherDirectImageModuleMap (f ∣_ UY).toShHom
              (Scheme.Modules.toRingedSpaceMap (f ⁻¹ᵁ UY).toScheme φ) p).val.app
            (Opposite.op (⊤ : Opens UY.toScheme))).hom
          (((Scheme.Modules.fromRingedSpaceMap UY.toScheme bc).val.app
              (Opposite.op (⊤ : Opens UY.toScheme))).hom xPull))))

/-- Additivity in the `I^n` factor of `tensorHigherDirectImageSection`. -/
theorem tensorHigherDirectImageSection_add_left (I : Y.IdealSheafData)
    [I.toModule.IsQuasicoherent] {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (p n m : ℕ) (U : (Opens Y)ᵒᵖ)
    (a a' : ((IdealSheafData.reesAlgebra I).obj (Int.ofNat n)).val.obj U)
    (x : (piece I f F p m).val.obj U) :
    tensorHigherDirectImageSection I f F p n m U (a + a') x =
      tensorHigherDirectImageSection I f F p n m U a x +
        tensorHigherDirectImageSection I f F p n m U a' x :=
  sorry

/-- Scalar-linearity in the `I^n` factor of `tensorHigherDirectImageSection`. -/
theorem tensorHigherDirectImageSection_smul_left (I : Y.IdealSheafData)
    [I.toModule.IsQuasicoherent] {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (p n m : ℕ) (U : (Opens Y)ᵒᵖ) (r : Y.sheaf.obj.obj U)
    (a : ((IdealSheafData.reesAlgebra I).obj (Int.ofNat n)).val.obj U)
    (x : (piece I f F p m).val.obj U) :
    tensorHigherDirectImageSection I f F p n m U (r • a) x =
      r • tensorHigherDirectImageSection I f F p n m U a x :=
  sorry

/-- Additivity in the higher-direct-image factor of `tensorHigherDirectImageSection`. -/
theorem tensorHigherDirectImageSection_add_right (I : Y.IdealSheafData)
    [I.toModule.IsQuasicoherent] {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (p n m : ℕ) (U : (Opens Y)ᵒᵖ)
    (a : ((IdealSheafData.reesAlgebra I).obj (Int.ofNat n)).val.obj U)
    (x x' : (piece I f F p m).val.obj U) :
    tensorHigherDirectImageSection I f F p n m U a (x + x') =
      tensorHigherDirectImageSection I f F p n m U a x +
        tensorHigherDirectImageSection I f F p n m U a x' :=
  sorry

/-- Scalar-linearity in the higher-direct-image factor of `tensorHigherDirectImageSection`. -/
theorem tensorHigherDirectImageSection_smul_right (I : Y.IdealSheafData)
    [I.toModule.IsQuasicoherent] {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (p n m : ℕ) (U : (Opens Y)ᵒᵖ) (r : Y.sheaf.obj.obj U)
    (a : ((IdealSheafData.reesAlgebra I).obj (Int.ofNat n)).val.obj U)
    (x : (piece I f F p m).val.obj U) :
    tensorHigherDirectImageSection I f F p n m U a (r • x) =
      r • tensorHigherDirectImageSection I f F p n m U a x :=
  sorry

/-- Sectionwise comparison `I^n(U) →ₗ R^p f_*(I^m F)(U) →ₗ R^p f_*(((I.comap f)^n) ⊗ I^m F)(U)`. -/
noncomputable def tensorHigherDirectImageBilinear (I : Y.IdealSheafData)
    [I.toModule.IsQuasicoherent] {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (p n m : ℕ) (U : (Opens Y)ᵒᵖ) :
    ((IdealSheafData.reesAlgebra I).obj (Int.ofNat n)).val.obj U →ₗ[Y.sheaf.obj.obj U]
      (piece I f F p m).val.obj U →ₗ[Y.sheaf.obj.obj U]
        (tensorPiece I f F p n m).val.obj U where
  toFun a :=
    { toFun := tensorHigherDirectImageSection I f F p n m U a
      map_add' := tensorHigherDirectImageSection_add_right I f F p n m U a
      map_smul' r x := tensorHigherDirectImageSection_smul_right I f F p n m U r a x }
  map_add' a a' :=
    LinearMap.ext fun x =>
      tensorHigherDirectImageSection_add_left I f F p n m U a a' x
  map_smul' r a :=
    LinearMap.ext fun x =>
      tensorHigherDirectImageSection_smul_left I f F p n m U r a x

/-- Restriction compatibility of the sectionwise comparison. -/
theorem tensorHigherDirectImageBilinear_naturality (I : Y.IdealSheafData)
    [I.toModule.IsQuasicoherent] {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (p n m : ℕ) {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V)
    (a : ((IdealSheafData.reesAlgebra I).obj (Int.ofNat n)).val.obj U)
    (x : (piece I f F p m).val.obj U) :
    ((tensorPiece I f F p n m).val.map i).hom
        (tensorHigherDirectImageSection I f F p n m U a x) =
      tensorHigherDirectImageSection I f F p n m V
        ((((IdealSheafData.reesAlgebra I).obj (Int.ofNat n)).val.map i).hom a)
        (((piece I f F p m).val.map i).hom x) :=
  sorry

/-- Canonical comparison `I^n ⊗ R^p f_*(I^m F) ⟶ R^p f_*(((I.comap f)^n) ⊗ I^m F)`. -/
noncomputable def tensorHigherDirectImageComparison (I : Y.IdealSheafData)
    [I.toModule.IsQuasicoherent] {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (p n m : ℕ) :
    ((IdealSheafData.reesAlgebra I).obj (Int.ofNat n) ⊗ piece I f F p m :
        Y.Modules) ⟶
      tensorPiece I f F p n m :=
  SectionBilinearMap.hom.{u, u}
    ({ app := tensorHigherDirectImageBilinear I f F p n m
       naturality := tensorHigherDirectImageBilinear_naturality I f F p n m } :
      SectionBilinearMap.{u, u} Y.sheaf
        ((IdealSheafData.reesAlgebra I).obj (Int.ofNat n))
        (piece I f F p m) (tensorPiece I f F p n m))

/-- Homogeneous action `I^n ⊗ R^p f_*(I^m F) ⟶ R^p f_*(I^{n+m} F)`, obtained by the
canonical comparison into `R^p f_*(((I.comap f)^n) ⊗ I^m F)` followed by higher direct
image of `productAction`. -/
noncomputable def actionHom (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p n m : ℕ) :
    ((IdealSheafData.reesAlgebra I).obj (Int.ofNat n) ⊗ piece I f F p m :
        Y.Modules) ⟶
      piece I f F p (n + m) :=
  tensorHigherDirectImageComparison I f F p n m ≫
    productActionDirectImage I f F p n m


/-- Homogeneous right action of a nonnegative Rees piece on a nonnegative higher-direct-image
piece, on local sections. -/
noncomputable def smulOfNat (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p i j : ℕ) (U : (Opens Y)ᵒᵖ) :
    (piece I f F p i).val.obj U →ₗ[Y.sheaf.obj.obj U]
      ((IdealSheafData.reesAlgebra I).obj (Int.ofNat j)).val.obj U →ₗ[Y.sheaf.obj.obj U]
        (piece I f F p (i + j)).val.obj U :=
  ((tensorSectionLinear Y.sheaf
        ((IdealSheafData.reesAlgebra I).obj (Int.ofNat j)) (piece I f F p i) U).compr₂
      ((actionHom I f F p j i ≫
          eqToHom (congrArg (piece I f F p) (Nat.add_comm j i))).val.app U).hom).flip

/-- On pure tensors, `actionHom` is higher direct image of `productAction` after the
canonical comparison; on affine opens this is the sheaf form of
`IdealPowerProduct.actionMap`. -/
theorem actionHom_spec (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p n m : ℕ)
    (U : (Opens Y)ᵒᵖ)
    (a : ((IdealSheafData.reesAlgebra I).obj (Int.ofNat n)).val.obj U)
    (x : (piece I f F p m).val.obj U) :
    ((actionHom I f F p n m).val.app U).hom (tensorSection Y.sheaf U a x) =
      ((productActionDirectImage I f F p n m).val.app U).hom
        (tensorHigherDirectImageSection I f F p n m U a x) :=
  sorry

/-- The degree-`n` piece of the graded higher-direct-image module, extended by zero in
negative degrees. -/
noncomputable def gradedModuleObj (I : Y.IdealSheafData) {X : Scheme.{u}}
    (f : X ⟶ Y) (F : X.Modules) (p : ℕ) (n : ℤ) : Y.Modules :=
  match n with
  | Int.ofNat k => piece I f F p k
  | Int.negSucc _ => zeroModule

/-- Nonnegative graded pieces are the corresponding higher direct images. -/
theorem gradedModuleObj_ofNat (I : Y.IdealSheafData) {X : Scheme.{u}}
    (f : X ⟶ Y) (F : X.Modules) (p n : ℕ) :
    gradedModuleObj I f F p n = piece I f F p n :=
  sorry

/-- Negative graded pieces are the zero module. -/
theorem gradedModuleObj_negSucc (I : Y.IdealSheafData) {X : Scheme.{u}}
    (f : X ⟶ Y) (F : X.Modules) (p n : ℕ) :
    gradedModuleObj I f F p (Int.negSucc n) = zeroModule :=
  sorry

/-- Homogeneous right action of the Rees algebra on the graded higher-direct-image module:
nonnegative action via `actionHom`, and zero if either degree is negative. -/
noncomputable def gradedModuleSmul (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ) (n m : ℤ)
    (U : (Opens Y)ᵒᵖ) :
    (gradedModuleObj I f F p n).val.obj U →ₗ[Y.sheaf.obj.obj U]
      ((IdealSheafData.reesAlgebra I).obj m).val.obj U →ₗ[Y.sheaf.obj.obj U]
        (gradedModuleObj I f F p (n + m)).val.obj U :=
  match n, m with
  | Int.ofNat i, Int.ofNat j => smulOfNat I f F p i j U
  | Int.negSucc _, _ => 0
  | Int.ofNat _, Int.negSucc _ => 0

/-- Nonnegative homogeneous action is `smulOfNat`. -/
theorem gradedModuleSmul_ofNat (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p i j : ℕ) (U : (Opens Y)ᵒᵖ) :
    gradedModuleSmul I f F p (Int.ofNat i) (Int.ofNat j) U =
      smulOfNat I f F p i j U :=
  sorry

/-- Restriction of the homogeneous action. -/
theorem gradedModule_map_smul (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ) {n m : ℤ}
    {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V)
    (x : (gradedModuleObj I f F p n).val.obj U)
    (a : ((IdealSheafData.reesAlgebra I).obj m).val.obj U) :
    ((gradedModuleObj I f F p (n + m)).val.map i).hom
        (gradedModuleSmul I f F p n m U x a) =
      gradedModuleSmul I f F p n m V
        (((gradedModuleObj I f F p n).val.map i).hom x)
        ((((IdealSheafData.reesAlgebra I).obj m).val.map i).hom a) :=
  sorry

/-- Associativity of the homogeneous action with Rees multiplication. -/
theorem gradedModule_smul_assoc (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ) (n m l : ℤ)
    (U : (Opens Y)ᵒᵖ)
    (x : (gradedModuleObj I f F p n).val.obj U)
    (a : ((IdealSheafData.reesAlgebra I).obj m).val.obj U)
    (b : ((IdealSheafData.reesAlgebra I).obj l).val.obj U) :
    HEq (gradedModuleSmul I f F p (n + m) l U
        (gradedModuleSmul I f F p n m U x a) b)
      (gradedModuleSmul I f F p n (m + l) U x
        ((IdealSheafData.reesAlgebra I).mul U m l a b)) :=
  sorry

/-- The degree-zero unit acts trivially. -/
theorem gradedModule_smul_one (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ) (n : ℤ)
    (U : (Opens Y)ᵒᵖ) (x : (gradedModuleObj I f F p n).val.obj U) :
    HEq (gradedModuleSmul I f F p n 0 U x ((IdealSheafData.reesAlgebra I).one U)) x :=
  sorry

/-- The graded `A`-module sheaf `M = ⨁_{n ≥ 0} R^p f_*(I^n F)` over the Rees algebra of `I`. -/
noncomputable def gradedModule (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ) :
    GradedModuleSheaf.{u, u} (IdealSheafData.reesAlgebra I) where
  obj := gradedModuleObj I f F p
  smul := gradedModuleSmul I f F p
  map_smul := gradedModule_map_smul I f F p
  smul_assoc := gradedModule_smul_assoc I f F p
  smul_one := gradedModule_smul_one I f F p

/-- Nonnegative components of the graded higher-direct-image module are the corresponding
higher direct images. -/
theorem gradedModule_obj_ofNat (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p n : ℕ) :
    (gradedModule I f F p).obj n = piece I f F p n :=
  sorry

/-- Negative components of the graded higher-direct-image module are zero. -/
theorem gradedModule_obj_negSucc (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
    {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p n : ℕ) :
    (gradedModule I f F p).obj (Int.negSucc n) = zeroModule :=
  sorry

/-- Every nonnegative higher-direct-image piece is quasi-coherent. -/
instance piece_isQuasicoherent (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
    {X : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p n : ℕ) :
    (piece I f F p n).IsQuasicoherent :=
  sorry

/-- Every nonnegative higher-direct-image piece is coherent. -/
instance piece_isCoherent (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
    {X : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p n : ℕ) :
    (piece I f F p n).IsCoherent :=
  sorry

variable {Y : Scheme.{u}} (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
variable {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ)

/-- For a proper morphism with locally Noetherian target, the graded higher direct images
of the powers of a quasi-coherent ideal times a coherent module are quasi-coherent. -/
instance isQuasicoherent [IsLocallyNoetherian Y] [IsProper f] [F.IsCoherent]
    (n : ℤ) : ((gradedModule I f F p).obj n).IsQuasicoherent :=
  sorry

/-- For a proper morphism with locally Noetherian target, the graded higher direct images
of the powers of a quasi-coherent ideal times a coherent module are locally of finite type
over the Rees algebra, with a finite homogeneous family uniform across all degrees. -/
theorem isFiniteType [IsLocallyNoetherian Y] [IsProper f] [F.IsCoherent] :
    GradedModuleSheaf.IsLocallyFiniteType.{u, u} (gradedModule I f F p) :=
  sorry

end IdealPowerCohomology
end AlgebraicGeometry.Scheme.Hom
