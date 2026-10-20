module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IntegerModules

/-!
# Constant-integer module sheaves and étale extension by zero

Étale extension by zero of constant integer module sheaves is compatible with
forgetting coefficients to abelian sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The universe-correct coefficient ring for sheaves of abelian groups modeled as
`ℤ`-modules. -/
abbrev integerModule : Type (u + 1) := ULift.{u + 1} ℤ

/-- `integerModule` is the universe lift of `ℤ`. -/
theorem integerModule_eq : integerModule = ULift.{u + 1} ℤ :=
  rfl

/-- Sheaves of abelian groups on algebraic-space étale sites, as `integerModule`-modules. -/
abbrev IntegerModuleCat := ModuleCat.{u + 1} integerModule

/-- Module-valued sheaves on the small étale topology of an algebraic space admit weak
sheafification. -/
instance smallEtaleTopology_hasWeakSheafify_integerModuleCat (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) IntegerModuleCat :=
  sorry

/-- Locally bijective morphisms of integer-module presheaves on the small étale site of an
algebraic space form a monoidal morphism property. -/
instance smallEtaleTopology_w_isMonoidal_integerModuleCat (X : AlgebraicSpace S) :
    ((smallEtaleTopology X).W :
        MorphismProperty ((smallEtaleSite X)ᵒᵖ ⥤ IntegerModuleCat)).IsMonoidal :=
  sorry

/-- Integer-module sheaves on the small étale site of an algebraic space admit binary
biproducts. -/
instance smallEtaleTopology_hasBinaryBiproducts_integerModuleCat (X : AlgebraicSpace S) :
    HasBinaryBiproducts (Sheaf (smallEtaleTopology X) IntegerModuleCat) :=
  sorry

/-- Coefficient change from `integerModule`-modules to abelian groups preserves sheaves on
the small étale topology of an algebraic space. -/
instance smallEtaleTopology_hasSheafCompose_integerModuleCat (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose
      (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1}) :=
  sorry

/-- Coefficient change from `integerModule`-modules to abelian groups preserves
sheafification on the small étale topology of an algebraic space. -/
instance smallEtaleTopology_preservesSheafification_integerModuleCat
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).PreservesSheafification
      (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1}) :=
  sorry

/-- Forgetting `integerModule`-modules to abelian groups preserves left Kan extensions
along the opposite of étale restriction. -/
instance etaleRestriction_op_preservesLeftKanExtensions_integerModuleCat
    {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions
      (etaleRestriction f).op :=
  fun F => { preserves := by intro F' α h; sorry }

/-- Extension by zero for sheaves of `integerModule`-modules, the coefficient model for
`⊗_ℤ`. -/
noncomputable abbrev moduleExtensionByZero {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    Sheaf (smallEtaleTopology U) IntegerModuleCat ⥤
      Sheaf (smallEtaleTopology X) IntegerModuleCat :=
  etaleExtensionByZero f IntegerModuleCat

/-- Module extension by zero is the generic étale extension functor on `IntegerModuleCat`. -/
theorem moduleExtensionByZero_def {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    moduleExtensionByZero f = etaleExtensionByZero f IntegerModuleCat :=
  rfl

/-- The constant sheaf of `integerModule`-modules on the small étale site of an algebraic
space. -/
noncomputable abbrev constantIntegerModuleSheaf (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) IntegerModuleCat :=
  (constantSheaf (smallEtaleTopology X) IntegerModuleCat).obj
    (.of integerModule integerModule)

/-- The constant integer module sheaf is the constant sheaf on `integerModule`. -/
theorem constantIntegerModuleSheaf_obj (X : AlgebraicSpace S) :
    constantIntegerModuleSheaf X =
      (constantSheaf (smallEtaleTopology X) IntegerModuleCat).obj
        (.of integerModule integerModule) :=
  rfl

/-- The sheaf `f_! underline(ℤ)` as an `integerModule`-module sheaf, obtained by étale
extension by zero of the constant integer module sheaf. -/
noncomputable abbrev moduleExtensionByZeroInteger {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    Sheaf (smallEtaleTopology X) IntegerModuleCat :=
  (moduleExtensionByZero f).obj (constantIntegerModuleSheaf U)

/-- `moduleExtensionByZeroInteger f` is module extension by zero of the constant integer
module sheaf. -/
theorem moduleExtensionByZeroInteger_obj {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    moduleExtensionByZeroInteger f =
      (moduleExtensionByZero f).obj (constantIntegerModuleSheaf U) :=
  rfl

/-- The constant `integerModule`-module sheaf forgets to the constant abelian integer
sheaf. -/
noncomputable def constantIntegerModuleSheaf_toAbelian (X : AlgebraicSpace S) :
    (sheafCompose (smallEtaleTopology X)
        (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})).obj
      (constantIntegerModuleSheaf X) ≅
      CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X) :=
  (constantCommuteCompose (smallEtaleTopology X)
      (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})).app
    (.of integerModule integerModule)

/-- The underlying abelian sheaf of `constantIntegerModuleSheaf` is `constantIntegerSheaf`. -/
theorem constantIntegerModuleSheaf_toAbelian_hom (X : AlgebraicSpace S) :
    (constantIntegerModuleSheaf_toAbelian X).hom =
      ((constantCommuteCompose (smallEtaleTopology X)
          (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})).app
        (.of integerModule integerModule)).hom :=
  rfl

/-- The underlying abelian sheaf of the module-valued extension by zero is abelian
extension by zero of the constant integer sheaf. -/
noncomputable def moduleExtensionByZeroInteger_toAbelian {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    (sheafCompose (smallEtaleTopology X)
        (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})).obj
      (moduleExtensionByZeroInteger f) ≅
      (abelianExtensionByZero f).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology U)) :=
  (Functor.sheafPullback.compSheafComposeIso (etaleRestriction f)
      (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})
      (smallEtaleTopology U) (smallEtaleTopology X)).app
    (constantIntegerModuleSheaf U) ≪≫
    (etaleExtensionByZero f AddCommGrpCat.{u + 1}).mapIso
      (constantIntegerModuleSheaf_toAbelian U)

/-- Forgetting coefficients on `moduleExtensionByZeroInteger f` recovers abelian extension
by zero of the constant integer sheaf on `U`. -/
theorem moduleExtensionByZeroInteger_toAbelian_hom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    (moduleExtensionByZeroInteger_toAbelian f).hom =
      ((Functor.sheafPullback.compSheafComposeIso (etaleRestriction f)
          (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})
          (smallEtaleTopology U) (smallEtaleTopology X)).app
        (constantIntegerModuleSheaf U) ≪≫
        (etaleExtensionByZero f AddCommGrpCat.{u + 1}).mapIso
          (constantIntegerModuleSheaf_toAbelian U)).hom :=
  rfl

/-- The two integer-module realizations of extension by zero have canonically
isomorphic underlying abelian sheaves. -/
noncomputable def moduleExtensionByZeroInteger_toSheafIso {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    (sheafCompose (smallEtaleTopology X)
        (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})).obj
      (moduleExtensionByZeroInteger f) ≅
      (SheafOfModules.toSheaf
        (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u}
          (constantIntegerRingSheaf X))).obj (extensionByZeroInteger f) :=
  moduleExtensionByZeroInteger_toAbelian f ≪≫ (extensionByZeroInteger_toSheafIso f).symm

/-- Integer-module presheaves admit pointwise right Kan extensions along the opposite
of étale restriction. -/
instance etaleRestriction_op_hasPointwiseRightKanExtension_integerModuleCat
    {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    (F : (smallEtaleSite U)ᵒᵖ ⥤ IntegerModuleCat.{u, u}) :
    (etaleRestriction f).op.HasPointwiseRightKanExtension F :=
  fun _ ↦ inferInstance

/-- The comparison isomorphism `ℤ̲_U ≅ f⁻¹ ℤ̲_X` of constant `integerModule`-module sheaves,
obtained by sheafifying the identification of constant presheaves along étale restriction. -/
noncomputable def constantIntegerModulePullbackIso {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    constantIntegerModuleSheaf U ≅
      (etaleRestrictionSheaf f IntegerModuleCat).obj (constantIntegerModuleSheaf X) :=
  let M := ModuleCat.of integerModule integerModule
  let h :
      (etaleRestriction f).op ⋙ (Functor.const (smallEtaleSite X)ᵒᵖ).obj M ≅
        (Functor.const (smallEtaleSite U)ᵒᵖ).obj M :=
    (Functor.constCompWhiskeringLeftIso (smallEtaleSite U)ᵒᵖ (etaleRestriction f).op).app M
  (presheafToSheaf (smallEtaleTopology U) IntegerModuleCat).mapIso h.symm ≪≫
    ((etaleRestriction f).pushforwardContinuousSheafificationCompatibility
        IntegerModuleCat (smallEtaleTopology U) (smallEtaleTopology X)).app
      ((Functor.const _).obj M)

/-- The forward comparison `ℤ̲_U ⟶ f⁻¹ ℤ̲_X` of constant `integerModule`-module sheaves. -/
noncomputable def constantIntegerModulePullbackHom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    constantIntegerModuleSheaf U ⟶
      (etaleRestrictionSheaf f IntegerModuleCat).obj (constantIntegerModuleSheaf X) :=
  (constantIntegerModulePullbackIso f).hom

/-- The reverse comparison `f⁻¹ ℤ̲_X ⟶ ℤ̲_U` of constant `integerModule`-module sheaves. -/
noncomputable def constantIntegerModulePullbackInv {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    (etaleRestrictionSheaf f IntegerModuleCat).obj (constantIntegerModuleSheaf X) ⟶
      constantIntegerModuleSheaf U :=
  (constantIntegerModulePullbackIso f).inv

/-- The constant integer module comparison is the sheafification of the constant-presheaf
identification along étale restriction. -/
theorem constantIntegerModulePullbackIso_hom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    (constantIntegerModulePullbackIso f).hom = constantIntegerModulePullbackHom f :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
