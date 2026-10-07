module

public import ReasLib.Algebra.Module.IdealPower.Submodule
public import ReasLib.Algebra.Module.IdealPower.Submodule.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.DerivedBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Difference
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Graded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.RegularSection.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.CartierTwist
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Pullback

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/-- The scheme module `p^*M(q)` attached to a finite module over `A ⧸ I ^ n`. -/
noncomputable abbrev quotientModuleTwist
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    {n : ℕ} (M : ModuleCat (A ⧸ I ^ n)) (q : ℤ) : X.Modules :=
  Scheme.Modules.twistByTensorPower
    (exceptionalIdeal I p).toModule
    ((Scheme.Modules.affineBaseModuleAssociatedFunctor A p).obj
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M)) q

/-- The quotient-module twist is the affine-base associated module tensored by the exceptional
integral power. -/
theorem quotientModuleTwist_def
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    {n : ℕ} (M : ModuleCat (A ⧸ I ^ n)) (q : ℤ) :
    quotientModuleTwist I p M q =
      Scheme.Modules.twistByTensorPower
        (exceptionalIdeal I p).toModule
        ((Scheme.Modules.affineBaseModuleAssociatedFunctor A p).obj
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M)) q := sorry

/-- The ringed-space tensor presentation of the quotient twist is used when converting its
concrete tensor transition back to the scheme-module category. -/
theorem quotientModuleTwist_ringedSpaceTensor
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    {n : ℕ} (M : ModuleCat (A ⧸ I ^ n)) (q : ℤ) :
    quotientModuleTwist I p M q =
      Scheme.Modules.fromRingedSpaceObj X
        (Scheme.Modules.toRingedSpaceObj X
          ((Scheme.Modules.affineBaseModuleAssociatedFunctor A p).obj
            ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M)) ⊗
          RingedSpace.InvertiblePower.sheaf
            (exceptionalIdeal I p).toSubobject.toModule q) := sorry

/-- The canonical section of the inverse exceptional twist, obtained from the effective Cartier
divisor section and the inverse tensor-power comparison. -/
noncomputable def inverseExceptionalSection
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] :
    (RingedSpace.InvertiblePower.sheaf
      (exceptionalIdeal I p).toSubobject.toModule (-1)).sections :=
  let L : X.toRingedSpace.Modules := (exceptionalIdeal I p).toSubobject.toModule
  let e : L ⟶ (SheafOfModules.unit X.toRingedSpace.ringCatSheaf) :=
    Scheme.Modules.toRingedSpaceMap X ((exceptionalIdeal I p).toSubobject.arrow)
  let c :
      (SheafOfModules.unit X.toRingedSpace.ringCatSheaf : X.toRingedSpace.Modules) ⟶
        (@ihom _ _ (RingedSpace.modulesMonoidalCategory X.toRingedSpace) L
          (MonoidalCategory.isInvertibleObject.closed L)).obj
          (SheafOfModules.unit X.toRingedSpace.ringCatSheaf) :=
    (RingedSpace.unitIsoTensorUnit X.toRingedSpace).hom ≫
      @MonoidalClosed.curry _ _ (RingedSpace.modulesMonoidalCategory X.toRingedSpace)
        L (SheafOfModules.unit X.toRingedSpace.ringCatSheaf) (𝟙_ _)
        (MonoidalCategory.isInvertibleObject.closed L) ((ρ_ L).hom ≫ e)
  (RingedSpace.InvertiblePower.sheaf
      (exceptionalIdeal I p).toSubobject.toModule (-1)).unitHomEquiv
    (c ≫
      (RingedSpace.InvertiblePower.negOneIso
        (exceptionalIdeal I p).toSubobject.toModule).inv)

/-- The canonical section of every negative exceptional integral power. -/
noncomputable def inverseExceptionalPowerSection
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (n : ℕ) :
    (RingedSpace.InvertiblePower.sheaf
      (exceptionalIdeal I p).toSubobject.toModule (Int.negSucc n)).sections :=
  match n with
  | 0 => inverseExceptionalSection I p
  | n + 1 =>
      RingedSpace.sectionFromTop
        (RingedSpace.InvertiblePower.sheaf
          (exceptionalIdeal I p).toSubobject.toModule (Int.negSucc (n + 1)))
        (((RingedSpace.InvertiblePower.indexIso
          (exceptionalIdeal I p).toSubobject.toModule
          (MonoidalCategory.InvertiblePower.Aux.negSuccEq n).symm).hom.val.app
            (Opposite.op ⊤)).hom
          (RingedSpace.InvertiblePower.mulSection
            (exceptionalIdeal I p).toSubobject.toModule (Opposite.op ⊤)
            (-1) (Int.negSucc n)
            (RingedSpace.sectionsEquivTop
              (RingedSpace.InvertiblePower.sheaf
                (exceptionalIdeal I p).toSubobject.toModule (-1))
              (inverseExceptionalSection I p))
            (RingedSpace.sectionsEquivTop
              (RingedSpace.InvertiblePower.sheaf
                (exceptionalIdeal I p).toSubobject.toModule (Int.negSucc n))
              (inverseExceptionalPowerSection I p n))))

/-- The canonical transition from twist `q` to the lower twist `q - r`, obtained by multiplying
with the canonical section of the inverse exceptional power. -/
noncomputable def canonicalTwistTransition
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    {n : ℕ} (M : ModuleCat (A ⧸ I ^ n)) (q : ℤ) (r : ℕ) :
    quotientModuleTwist I p M q ⟶
      quotientModuleTwist I p M (q - (r : ℤ)) :=
  match r with
  | 0 =>
      eqToHom
        (congrArg (fun d ↦ quotientModuleTwist I p M d) (Int.sub_zero q).symm)
  | k + 1 =>
      let L : X.toRingedSpace.Modules := (exceptionalIdeal I p).toSubobject.toModule
      let F : X.toRingedSpace.Modules :=
        Scheme.Modules.toRingedSpaceObj X
          ((Scheme.Modules.affineBaseModuleAssociatedFunctor A p).obj
            ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M))
      let f₀ :
          F ⊗
              RingedSpace.InvertiblePower.sheaf L q ⟶
            F ⊗
              RingedSpace.InvertiblePower.sheaf L
            (q - ((k + 1 : ℕ) : ℤ)) :=
        (𝟙 F ⊗ₘ
          (RingedSpace.tensorSectionHom
            (RingedSpace.InvertiblePower.sheaf L q)
            (RingedSpace.InvertiblePower.sheaf L (Int.negSucc k))
            (inverseExceptionalPowerSection I p k) ≫
            (RingedSpace.InvertiblePower.addIso L q (Int.negSucc k)).hom ≫
            (RingedSpace.InvertiblePower.indexIso L
              ((congrArg (fun z : ℤ ↦ q + z) (Int.negSucc_eq k)).trans
                (@Int.sub_eq_add_neg q ((k + 1 : ℕ) : ℤ)).symm)).hom))
      eqToHom (quotientModuleTwist_ringedSpaceTensor I p M q) ≫
        Scheme.Modules.fromRingedSpaceMap X f₀ ≫
        eqToHom (quotientModuleTwist_ringedSpaceTensor I p M
          (q - ((k + 1 : ℕ) : ℤ))).symm

/-- The canonical transition is the identity at zero degree. -/
theorem canonicalTwistTransition_zero
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    {n : ℕ} (M : ModuleCat (A ⧸ I ^ n)) (q : ℤ) :
    canonicalTwistTransition I p M q 0 =
      eqToHom (congrArg (fun d ↦ quotientModuleTwist I p M d) (Int.sub_zero q).symm) := sorry

/-- The canonical transitions compose along successive lower twist steps, with the displayed
integer-index equality used to identify the two target objects. -/
theorem canonicalTwistTransition_comp
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    {n : ℕ} (M : ModuleCat (A ⧸ I ^ n)) (q : ℤ) (r s : ℕ)
    (h : q - (r : ℤ) - (s : ℤ) = q - ((r + s : ℕ) : ℤ)) :
    canonicalTwistTransition I p M q r ≫
        canonicalTwistTransition I p M (q - (r : ℤ)) s ≫
        eqToHom (congrArg (fun d ↦ quotientModuleTwist I p M d) h) =
      canonicalTwistTransition I p M q (r + s) := sorry

end AlgebraicGeometry.IsBlowup
