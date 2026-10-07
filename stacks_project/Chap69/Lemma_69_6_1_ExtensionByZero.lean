module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import stacks_project.Chap65.Lemma_65_8_4_Coproduct
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_18_12_Restriction
public import stacks_project.Chap69.Definition_69_6_2_ExtensionByZero
public import stacks_project.Chap69.Definition_69_6_2_Koszul

/-!
# Integer-module model of étale extension by zero

The source-facing functor `f_!` on algebraic-space small étale sites is the sheaf
pullback of étale restriction already owned by Definition 69.6.2. Integer coefficients
used for `⊗_ℤ` are sheaves of `ULift ℤ`-modules; the underlying abelian sheaf is
identified with `abelianExtensionByZero` of the constant integer sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The universe-correct coefficient ring for sheaves of abelian groups modeled as
`ℤ`-modules. -/
abbrev integerModule : Type (u + 1) := ULift.{u + 1} ℤ

/-- `integerModule` is the universe lift of `ℤ`. -/
theorem integerModule_eq : integerModule = ULift.{u + 1} ℤ :=
  sorry

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
  sorry

/-- Extension by zero for sheaves of `integerModule`-modules, the coefficient model that
owns `⊗_ℤ`. -/
noncomputable abbrev moduleExtensionByZero {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    Sheaf (smallEtaleTopology U) IntegerModuleCat ⥤
      Sheaf (smallEtaleTopology X) IntegerModuleCat :=
  etaleExtensionByZero f IntegerModuleCat

/-- Module extension by zero is the generic étale extension functor on `IntegerModuleCat`. -/
theorem moduleExtensionByZero_def {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    moduleExtensionByZero f = etaleExtensionByZero f IntegerModuleCat :=
  sorry

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
  sorry

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
  sorry

/-- The constant `integerModule`-module sheaf forgets to the constant abelian integer
sheaf. -/
noncomputable def constantIntegerModuleSheaf_toAbelian (X : AlgebraicSpace S) :
    (sheafCompose (smallEtaleTopology X)
        (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})).obj
      (constantIntegerModuleSheaf X) ≅ constantIntegerSheaf X :=
  (constantCommuteCompose (smallEtaleTopology X)
      (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})).app
    (.of integerModule integerModule)

/-- The underlying abelian sheaf of `constantIntegerModuleSheaf` is `constantIntegerSheaf`. -/
theorem constantIntegerModuleSheaf_toAbelian_hom (X : AlgebraicSpace S) :
    (constantIntegerModuleSheaf_toAbelian X).hom =
      ((constantCommuteCompose (smallEtaleTopology X)
          (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})).app
        (.of integerModule integerModule)).hom :=
  sorry

/-- The underlying abelian sheaf of the module-valued extension by zero is abelian
extension by zero of the constant integer sheaf. -/
noncomputable def moduleExtensionByZeroInteger_toAbelian {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    (sheafCompose (smallEtaleTopology X)
        (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})).obj
      (moduleExtensionByZeroInteger f) ≅
      (abelianExtensionByZero f).obj (constantIntegerSheaf U) :=
  (Functor.sheafPullback.compSheafComposeIso (etaleRestriction f)
      (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})
      (smallEtaleTopology U) (smallEtaleTopology X)).app
    (constantIntegerModuleSheaf U) ≪≫
    (etaleExtensionByZero f AddCommGrpCat.{u + 1}).mapIso
      (constantIntegerModuleSheaf_toAbelian U)

/-- Forgetting coefficients on `moduleExtensionByZeroInteger f` recovers abelian extension
by zero of `constantIntegerSheaf U`. -/
theorem moduleExtensionByZeroInteger_toAbelian_hom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    (moduleExtensionByZeroInteger_toAbelian f).hom =
      ((Functor.sheafPullback.compSheafComposeIso (etaleRestriction f)
          (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})
          (smallEtaleTopology U) (smallEtaleTopology X)).app
        (constantIntegerModuleSheaf U) ≪≫
        (etaleExtensionByZero f AddCommGrpCat.{u + 1}).mapIso
          (constantIntegerModuleSheaf_toAbelian U)).hom :=
  sorry

/-- The underlying abelian sheaf of Koszul's `extensionByZeroInteger f` agrees with the
forgetful image of `moduleExtensionByZeroInteger f`. -/
theorem moduleExtensionByZeroInteger_toSheaf {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    (sheafCompose (smallEtaleTopology X)
        (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})).obj
      (moduleExtensionByZeroInteger f) =
      (SheafOfModules.toSheaf (integerRingSheaf X)).obj (extensionByZeroInteger f) :=
  sorry

/-- The `Fin 2`-indexed family with values `U1` and `U2`. -/
def finTwo (U1 U2 : AlgebraicSpace S) (i : Fin 2) : AlgebraicSpace S :=
  match i with
  | 0 => U1
  | 1 => U2

/-- The `Fin 2`-indexed family of morphisms `f1, f2` into `X`. -/
def finTwoHom {X U1 U2 : AlgebraicSpace S} (f1 : U1 ⟶ X) (f2 : U2 ⟶ X)
    (i : Fin 2) : finTwo U1 U2 i ⟶ X :=
  match i with
  | 0 => f1
  | 1 => f2

/-- The zero component of `finTwo` is the first space. -/
theorem finTwo_zero (U1 U2 : AlgebraicSpace S) : finTwo U1 U2 0 = U1 :=
  sorry

/-- The zero component of `finTwoHom` is `f1`. -/
theorem finTwoHom_zero {X U1 U2 : AlgebraicSpace S} (f1 : U1 ⟶ X) (f2 : U2 ⟶ X) :
    finTwoHom f1 f2 0 = f1 :=
  sorry

/-- The binary coproduct of algebraic spaces as `coproduct` of a `Fin 2` family. -/
noncomputable abbrev binaryCoproduct (U1 U2 : AlgebraicSpace S) : AlgebraicSpace S :=
  coproduct (finTwo U1 U2)

/-- The binary coproduct is `coproduct` of `finTwo U1 U2`. -/
theorem binaryCoproduct_eq (U1 U2 : AlgebraicSpace S) :
    binaryCoproduct U1 U2 = coproduct (finTwo U1 U2) :=
  sorry

/-- The structure morphism `U1 ⨿ U2 ⟶ X` induced by a pair of morphisms into `X`. -/
noncomputable def coproductStructure {X U1 U2 : AlgebraicSpace S}
    (f1 : U1 ⟶ X) (f2 : U2 ⟶ X) :
    binaryCoproduct U1 U2 ⟶ X :=
  coproductDesc (finTwoHom f1 f2)

/-- The structure morphism of a binary coproduct is `coproductDesc` of `finTwoHom`. -/
theorem coproductStructure_eq {X U1 U2 : AlgebraicSpace S} (f1 : U1 ⟶ X) (f2 : U2 ⟶ X) :
    coproductStructure f1 f2 = coproductDesc (finTwoHom f1 f2) :=
  sorry

/-- The coproduct of two étale morphisms of algebraic spaces is étale. -/
instance etale_coproductDesc {X U1 U2 : AlgebraicSpace S} (f1 : U1 ⟶ X) (f2 : U2 ⟶ X)
    [Etale f1] [Etale f2] : Etale (coproductDesc (finTwoHom f1 f2)) :=
  sorry

/-- Each component of a pair of étale morphisms is étale. -/
instance etale_finTwoHom {X U1 U2 : AlgebraicSpace S} (f1 : U1 ⟶ X) (f2 : U2 ⟶ X)
    (i : Fin 2) [Etale f1] [Etale f2] : Etale (finTwoHom f1 f2 i) :=
  sorry

/-- Coproduct inclusions of algebraic spaces are étale. -/
instance etale_coproductι {I : Type} [Small.{u} I] (F : I → AlgebraicSpace S) (i : I) :
    Etale (coproductι F i) :=
  sorry

/-- The first projection of a fibre product of étale morphisms is étale. -/
instance etale_pullback_fst {X U1 U2 : AlgebraicSpace S} (f1 : U1 ⟶ X) (f2 : U2 ⟶ X)
    [HasPullback f1 f2] [Etale f2] : Etale (pullback.fst f1 f2) :=
  Etale.fst_of_isPullback (IsPullback.of_hasPullback f1 f2)

/-- The structure morphism `U1 ×_X U2 ⟶ X` of a fibre product of étale morphisms is étale. -/
instance etale_pullbackStructure {X U1 U2 : AlgebraicSpace S} (f1 : U1 ⟶ X) (f2 : U2 ⟶ X)
    [HasPullback f1 f2] [Etale f1] [Etale f2] :
    Etale (pullback.fst f1 f2 ≫ f1) :=
  inferInstance

/-- The structure morphism of `U1 ×_X U2` over `X` is `pullback.fst f1 f2 ≫ f1`. -/
theorem pullbackStructure_eq {X U1 U2 : AlgebraicSpace S} (f1 : U1 ⟶ X) (f2 : U2 ⟶ X)
    [HasPullback f1 f2] :
    pullback.fst f1 f2 ≫ f1 = pullback.snd f1 f2 ≫ f2 :=
  pullback.condition

/-- Étale restriction along a composite is the composite of étale restrictions. -/
noncomputable def etaleRestrictionCompIso {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Etale f] [Etale g] :
    etaleRestriction (f ≫ g) ≅ etaleRestriction f ⋙ etaleRestriction g :=
  NatIso.ofComponents
    (fun U ↦ MorphismProperty.CostructuredArrow.isoMk (Iso.refl U.left) trivial trivial sorry)
    sorry

/-- Right Kan extensions along the opposite of étale restriction exist on the small
étale sites of algebraic spaces. -/
instance etaleRestriction_op_hasPointwiseRightKanExtension
    {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    {A : Type v} [Category.{w} A] (F : (smallEtaleSite U)ᵒᵖ ⥤ A) :
    (etaleRestriction f).op.HasPointwiseRightKanExtension F :=
  sorry

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
  sorry

end AlgebraicGeometry.AlgebraicSpace
