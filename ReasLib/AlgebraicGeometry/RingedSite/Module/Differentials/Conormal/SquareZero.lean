/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Derivation.AdditiveMap
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Module
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal

/-!
# Conormal modules of square-zero extensions

The conormal sheaf of a locally surjective square-zero extension maps canonically into its
kernel module. Differences of compatible lifts that agree on the source kernel descend through
this map to relative derivations.
-/

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe c v w

namespace SheafOfModules.RingedSite.SquareZeroExtension

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {R B B₀ A Q : Sheaf J CommRingCat.{w}}

/-- The additive map from a section of a kernel ideal to the same section in the canonical
target-ring module carried by a locally surjective square-zero extension preserves addition. -/
private theorem kernelSectionToTarget_add (pi : A ⟶ Q)
    [CategoryTheory.Sheaf.IsLocallySurjective pi]
    (hpi : KernelIdeal.IsSquareZero pi) (U : Cᵒᵖ)
    (x y : KernelIdeal.sectionIdeal pi U) :
    (hpi.targetModuleForgetIso
          (inferInstance : IsIso (KernelIdeal.quotientComparison pi))).inv.hom.app U
        ((KernelIdeal.sectionsIso pi U).inv (x + y)) =
      (hpi.targetModuleForgetIso
          (inferInstance : IsIso (KernelIdeal.quotientComparison pi))).inv.hom.app U
          ((KernelIdeal.sectionsIso pi U).inv x) +
        (hpi.targetModuleForgetIso
          (inferInstance : IsIso (KernelIdeal.quotientComparison pi))).inv.hom.app U
          ((KernelIdeal.sectionsIso pi U).inv y) := sorry

/-- The canonical map from kernel sections to the target-ring module respects scalar
multiplication. -/
private theorem kernelSectionToTarget_smul (pi : A ⟶ Q)
    [CategoryTheory.Sheaf.IsLocallySurjective pi]
    (hpi : KernelIdeal.IsSquareZero pi) (U : Cᵒᵖ)
    (r : A.obj.obj U) (x : KernelIdeal.sectionIdeal pi U) :
    let f : KernelIdeal.sectionIdeal pi U →
        ((restrictionAlong pi).obj
          (hpi.targetModule
            (inferInstance : IsIso (KernelIdeal.quotientComparison pi)))).val.obj U :=
      fun y ↦
        (hpi.targetModuleForgetIso
            (inferInstance : IsIso (KernelIdeal.quotientComparison pi))).inv.hom.app U
          ((KernelIdeal.sectionsIso pi U).inv y)
    f (r • x) = r • f x := sorry

/-- A kernel section, regarded in the canonical module over the target of a square-zero
extension. -/
@[no_expose] noncomputable def kernelSectionToTarget (pi : A ⟶ Q)
    [CategoryTheory.Sheaf.IsLocallySurjective pi]
    (hpi : KernelIdeal.IsSquareZero pi) (U : Cᵒᵖ) :
    KernelIdeal.sectionIdeal pi U →ₗ[A.obj.obj U]
      ((restrictionAlong pi).obj
        (hpi.targetModule
          (inferInstance : IsIso (KernelIdeal.quotientComparison pi)))).val.obj U where
  toFun x :=
    (hpi.targetModuleForgetIso
        (inferInstance : IsIso (KernelIdeal.quotientComparison pi))).inv.hom.app U
      ((KernelIdeal.sectionsIso pi U).inv x)
  map_add' := kernelSectionToTarget_add pi hpi U
  map_smul' := kernelSectionToTarget_smul pi hpi U

/-- Products in the square-zero kernel vanish under its canonical map to the target-ring
module. -/
private theorem kernelSectionToTarget_mul (pi : A ⟶ Q)
    [CategoryTheory.Sheaf.IsLocallySurjective pi]
    (hpi : KernelIdeal.IsSquareZero pi) (U : Cᵒᵖ)
    (x y : KernelIdeal.sectionIdeal pi U) :
    kernelSectionToTarget pi hpi U (x * y) = 0 := sorry

/-- The sectionwise map from the conormal quotient to the kernel module of a square-zero
extension. -/
@[no_expose] noncomputable def conormalSectionToTarget (pi : A ⟶ Q)
    [CategoryTheory.Sheaf.IsLocallySurjective pi]
    (hpi : KernelIdeal.IsSquareZero pi) (U : Cᵒᵖ) :
    conormalObj pi U →ₗ[A.obj.obj U]
      ((restrictionAlong pi).obj
        (hpi.targetModule
          (inferInstance : IsIso (KernelIdeal.quotientComparison pi)))).val.obj U :=
  Ideal.Cotangent.lift (kernelSectionToTarget pi hpi U)
    (kernelSectionToTarget_mul pi hpi U)

/-- The sectionwise square-zero conormal-to-kernel maps commute with restrictions. -/
private theorem conormalSectionToTarget_naturality (pi : A ⟶ Q)
    [CategoryTheory.Sheaf.IsLocallySurjective pi]
    (hpi : KernelIdeal.IsSquareZero pi) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (conormalPresheaf pi).map f ≫
        (ModuleCat.restrictScalars (((ringSheaf J A).obj.map f).hom)).map
          (ConcreteCategory.ofHom (conormalSectionToTarget pi hpi V)) =
      ConcreteCategory.ofHom (conormalSectionToTarget pi hpi U) ≫
        ((restrictionAlong pi).obj
          (hpi.targetModule
            (inferInstance : IsIso (KernelIdeal.quotientComparison pi)))).val.map f := sorry

/-- The presheaf map from conormal classes to the target-ring module of a square-zero
extension. -/
@[no_expose] noncomputable def conormalPresheafToTarget (pi : A ⟶ Q)
    [CategoryTheory.Sheaf.IsLocallySurjective pi]
    (hpi : KernelIdeal.IsSquareZero pi) :
    conormalPresheaf pi ⟶
      ((restrictionAlong pi).obj
        (hpi.targetModule
          (inferInstance : IsIso (KernelIdeal.quotientComparison pi)))).val where
  app U := ConcreteCategory.ofHom (conormalSectionToTarget pi hpi U)
  naturality f := conormalSectionToTarget_naturality pi hpi f

/-- The sheafified conormal quotient maps to the restricted canonical kernel module. -/
@[no_expose] noncomputable def conormalOverSourceToTarget (pi : A ⟶ Q)
    [CategoryTheory.Sheaf.IsLocallySurjective pi]
    (hpi : KernelIdeal.IsSquareZero pi) :
    conormalSourceOverSource pi ⟶
      (restrictionAlong pi).obj
        (hpi.targetModule
          (inferInstance : IsIso (KernelIdeal.quotientComparison pi))) :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J A).obj)).homEquiv _ _).symm
    (conormalPresheafToTarget pi hpi)

/-- The conormal sheaf of a locally surjective square-zero extension maps canonically to its
kernel module over the target ring sheaf. -/
@[no_expose] noncomputable def conormalToTarget (pi : A ⟶ Q)
    [CategoryTheory.Sheaf.IsLocallySurjective pi]
    (hpi : KernelIdeal.IsSquareZero pi) :
    conormalSource pi ⟶
      hpi.targetModule
        (inferInstance : IsIso (KernelIdeal.quotientComparison pi)) :=
  ((extendRestrictAdj pi).homEquiv _ _).symm
    (conormalOverSourceToTarget pi hpi)

/-- Under the extension-restriction adjunction, `conormalToTarget` corresponds to the
conormal map constructed over the source ring sheaf. -/
theorem conormalToTarget_adjunct (pi : A ⟶ Q)
    [CategoryTheory.Sheaf.IsLocallySurjective pi]
    (hpi : KernelIdeal.IsSquareZero pi) :
    ((extendRestrictAdj pi).homEquiv _ _) (conormalToTarget pi hpi) =
      conormalOverSourceToTarget pi hpi := sorry

/-- The canonical additive inclusion `ker(pi) / ker(pi)² ⟶ A` for a locally surjective
square-zero extension `pi : A ⟶ Q`. -/
noncomputable def conormalInclusion (pi : A ⟶ Q)
    [CategoryTheory.Sheaf.IsLocallySurjective pi]
    (hpi : KernelIdeal.IsSquareZero pi) :
    (SheafOfModules.toSheaf (ringSheaf J Q)).obj (conormalSource pi) ⟶
      (SheafOfModules.toSheaf (ringSheaf J A)).obj (unitModule J A) :=
  (SheafOfModules.toSheaf (ringSheaf J Q)).map (conormalToTarget pi hpi) ≫
    (hpi.targetModuleForgetIso
      (inferInstance : IsIso (KernelIdeal.quotientComparison pi))).hom ≫
    (SheafOfModules.toSheaf (ringSheaf J A)).map (KernelIdeal.ι pi)

/-- The square-zero conormal inclusion sends the class of a kernel section to that section in
the ambient ring sheaf. -/
theorem conormalInclusion_apply (pi : A ⟶ Q)
    [CategoryTheory.Sheaf.IsLocallySurjective pi]
    (hpi : KernelIdeal.IsSquareZero pi) (U : Cᵒᵖ)
    (x : conormalIdeal pi U) :
    (conormalInclusion pi hpi).hom.app U
        ((conormalSourcePresheafUnit pi).app U
          ((conormalIdeal pi U).toCotangent x)) = x.1 := sorry

/-- The difference of two compatible lifts descends through a locally surjective source
quotient once the lifts agree on its kernel. -/
theorem exists_descendedDifference (alpha : R ⟶ B) (alpha₀ : R ⟶ B₀)
    (rho : B ⟶ B₀) [CategoryTheory.Sheaf.IsLocallySurjective rho]
    (beta : R ⟶ A) (pi : A ⟶ Q) [CategoryTheory.Sheaf.IsLocallySurjective pi]
    (f : B₀ ⟶ Q) (l l' : B ⟶ A) (hpi : KernelIdeal.IsSquareZero pi)
    (halpha : alpha ≫ rho = alpha₀)
    (hl : IsLift alpha beta pi (rho ≫ f) l)
    (hl' : IsLift alpha beta pi (rho ≫ f) l')
    (hkernel : ∀ U : Cᵒᵖ, ∀ x : (KernelIdeal.sheaf rho).val.obj U,
      l.hom.app U (KernelIdeal.ιApp rho U x) =
        l'.hom.app U (KernelIdeal.ιApp rho U x)) :
    ∃ D : Der[alpha₀ ; (restrictionAlong f).obj (conormalSource pi)],
      ∀ (U : Cᵒᵖ) (x : B.obj.obj U),
        (additiveDifference l l').hom.app U x =
          (conormalInclusion pi hpi).hom.app U (D.d (rho.hom.app U x)) := sorry

end SheafOfModules.RingedSite.SquareZeroExtension
