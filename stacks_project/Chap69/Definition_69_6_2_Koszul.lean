module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Ring.ULift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Constant
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Koszul
public import ReasLib.Algebra.Category.Ring.Sheaf
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap69.Definition_69_6_2_ExtensionByZero

/-!
# Truncated Koszul complex of the étale trace

For a surjective étale morphism `f : U ⟶ X` of algebraic spaces, the complex
`K^•(f)` has terms `K^n = ∧^{n+1} (f_! ℤ̲)` over the constant integer ring sheaf,
with Koszul differentials of the trace `Tr_f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The constant sheaf of rings `ℤ̲` on the small étale site of an algebraic space. -/
noncomputable abbrev constantIntegerRingSheaf (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  (constantSheaf (smallEtaleTopology X) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} ℤ))

/-- The constant integer ring sheaf is the constant sheaf with value `ULift ℤ`. -/
theorem constantIntegerRingSheaf_def (X : AlgebraicSpace S) :
    constantIntegerRingSheaf X =
      (constantSheaf (smallEtaleTopology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} ℤ)) :=
  sorry

/-- The underlying ring sheaf of the constant integer ring sheaf. -/
noncomputable abbrev integerRingSheaf (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) RingCat.{u + 1} :=
  (sheafCompose (smallEtaleTopology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (constantIntegerRingSheaf X)

/-- The underlying ring sheaf is coefficient change of the constant integer ring
sheaf. -/
theorem integerRingSheaf_def (X : AlgebraicSpace S) :
    integerRingSheaf X =
      (sheafCompose (smallEtaleTopology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (constantIntegerRingSheaf X) :=
  sorry

/-- The comparison morphism `ℤ̲_U ⟶ f⁻¹ ℤ̲_X` of constant commutative ring sheaves. -/
noncomputable def constantIntegerRingPullbackHom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    constantIntegerRingSheaf U ⟶
      (etaleRestrictionSheaf f CommRingCat.{u + 1}).obj (constantIntegerRingSheaf X) :=
  let M := CommRingCat.of (ULift.{u + 1} ℤ)
  let adjU := sheafificationAdjunction (smallEtaleTopology U) CommRingCat.{u + 1}
  let adjX := sheafificationAdjunction (smallEtaleTopology X) CommRingCat.{u + 1}
  (adjU.homEquiv ((Functor.const _).obj M)
      ((etaleRestrictionSheaf f CommRingCat.{u + 1}).obj
        (constantIntegerRingSheaf X))).symm
    ((Functor.constCompWhiskeringLeftIso ((smallEtaleSite U)ᵒᵖ)
          (C := CommRingCat.{u + 1}) (etaleRestriction f).op).inv.app M ≫
      Functor.whiskerLeft (etaleRestriction f).op (adjX.unit.app ((Functor.const _).obj M)))

/-- The comparison of constant integer ring sheaves is an isomorphism. -/
instance isIso_constantIntegerRingPullbackHom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    IsIso (constantIntegerRingPullbackHom f) :=
  sorry

/-- The constant integer ring comparison is an isomorphism of sheaves. -/
theorem constantIntegerRingPullbackHom_spec {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    IsIso (constantIntegerRingPullbackHom f) :=
  sorry

/-- The ring-sheaf morphism `ℤ̲_U ⟶ f⁻¹ ℤ̲_X` obtained by applying coefficient
change to the constant integer comparison. -/
noncomputable def constantIntegerRingRestrictionHom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    integerRingSheaf U ⟶
      (etaleRestrictionSheaf f RingCat.{u + 1}).obj (integerRingSheaf X) :=
  (sheafCompose (smallEtaleTopology U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (constantIntegerRingPullbackHom f)


/-- The underlying ring comparison is coefficient change of the constant integer
ring comparison. -/
theorem constantIntegerRingRestrictionHom_def {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    constantIntegerRingRestrictionHom f =
      (sheafCompose (smallEtaleTopology U)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (constantIntegerRingPullbackHom f) :=
  sorry

/-- Coefficient change from commutative rings to rings preserves sheafification on the
small étale topology of an algebraic space. -/
instance smallEtaleTopology_preservesSheafification_commRingToRing
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  sorry

/-- Coefficient change from rings to abelian groups preserves sheafification on the
small étale topology of an algebraic space. -/
instance smallEtaleTopology_preservesSheafification_ringToAddCommGrp
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).PreservesSheafification
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  sorry

/-- Locally bijective morphisms of ring-valued sheaves on the small étale topology of an
algebraic space are the sheafification equivalences. -/
instance smallEtaleTopology_wEqualsLocallyBijective_ringCat
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).WEqualsLocallyBijective RingCat.{u + 1} :=
  sorry

/-- Universe-lifted integers act on an abelian group through the canonical ring
equivalence `ULift ℤ ≃+* ℤ`. -/
noncomputable instance instModuleULiftIntOfAddCommGrpCat
    (A : AddCommGrpCat.{u + 1}) : Module (ULift.{u + 1} ℤ) A :=
  Module.compHom A (ULift.ringEquiv (R := ℤ)).toRingHom

/-- The constant integer ring presheaf acts on any abelian presheaf on a small
étale site. -/
noncomputable instance instModuleConstIntegerRingPresheaf {X : AlgebraicSpace S}
    (F : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (Y : (smallEtaleSite X)ᵒᵖ) :
    Module
      (((Functor.const (smallEtaleSite X)ᵒᵖ).obj
          (RingCat.of (ULift.{u + 1} ℤ))).obj Y)
      (F.obj Y) :=
  Module.compHom (F.obj Y) (ULift.ringEquiv (R := ℤ)).toRingHom

/-- The constant integer ring sheaf, viewed as a constant sheaf of possibly
noncommutative rings. -/
noncomputable def integerRingSheafIsoConstant (X : AlgebraicSpace S) :
    integerRingSheaf X ≅
      (constantSheaf (smallEtaleTopology X) RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1} ℤ)) :=
  (constantCommuteCompose (smallEtaleTopology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
    (CommRingCat.of (ULift.{u + 1} ℤ))

/-- The identification of `integerRingSheaf` with the constant `RingCat`-valued
integer sheaf is `constantCommuteCompose`. -/
theorem integerRingSheafIsoConstant_hom (X : AlgebraicSpace S) :
    (integerRingSheafIsoConstant X).hom =
      ((constantCommuteCompose (smallEtaleTopology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
        (CommRingCat.of (ULift.{u + 1} ℤ))).hom :=
  sorry

/-- The underlying abelian presheaf of an abelian sheaf on `X_étale`, regarded as a
module over the constant integer ring presheaf. -/
noncomputable def abelianSheaf_constantIntegerPresheaf {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    PresheafOfModules
      ((Functor.const (smallEtaleSite X)ᵒᵖ).obj (RingCat.of (ULift.{u + 1} ℤ))) :=
  PresheafOfModules.ofPresheaf F.obj sorry

/-- The underlying abelian presheaf of `abelianSheaf_constantIntegerPresheaf F`
is the underlying presheaf of `F`. -/
theorem abelianSheaf_constantIntegerPresheaf_presheaf {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (abelianSheaf_constantIntegerPresheaf F).presheaf = F.obj :=
  sorry

/-- The constant integer ring presheaf maps to `integerRingSheaf` by sheafifying
and identifying the constant `RingCat`-valued integer sheaf. -/
noncomputable def constantIntegerRingPresheafToSheaf (X : AlgebraicSpace S) :
    (Functor.const (smallEtaleSite X)ᵒᵖ).obj (RingCat.of (ULift.{u + 1} ℤ)) ⟶
      (integerRingSheaf X).obj :=
  Sheaf.ConstantModule.ringMap (J := smallEtaleTopology X) (R := ULift.{u + 1} ℤ) ≫
    (integerRingSheafIsoConstant X).inv.hom

/-- `constantIntegerRingPresheafToSheaf` is locally injective. -/
instance isLocallyInjective_constantIntegerRingPresheafToSheaf
    (X : AlgebraicSpace S) :
    Presheaf.IsLocallyInjective (smallEtaleTopology X)
      (constantIntegerRingPresheafToSheaf X) :=
  sorry

/-- `constantIntegerRingPresheafToSheaf` is locally surjective. -/
instance isLocallySurjective_constantIntegerRingPresheafToSheaf
    (X : AlgebraicSpace S) :
    Presheaf.IsLocallySurjective (smallEtaleTopology X)
      (constantIntegerRingPresheafToSheaf X) :=
  sorry

/-- The sheaf of `ℤ̲_X`-modules associated to an abelian sheaf, obtained by
sheafifying the constant-integer module structure along
`constantIntegerRingPresheafToSheaf`. -/
noncomputable def abelianSheaf_integerModules {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    SheafOfModules.{u + 1} (integerRingSheaf X) :=
  (PresheafOfModules.sheafification (constantIntegerRingPresheafToSheaf X)).obj
    (abelianSheaf_constantIntegerPresheaf F)

/-- `abelianSheaf_integerModules` is module sheafification of the constant-integer
module presheaf. -/
theorem abelianSheaf_integerModules_def {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    abelianSheaf_integerModules F =
      (PresheafOfModules.sheafification (constantIntegerRingPresheafToSheaf X)).obj
        (abelianSheaf_constantIntegerPresheaf F) :=
  sorry

/-- The underlying abelian sheaf of `abelianSheaf_integerModules F` is `F`. -/
noncomputable def abelianSheaf_integerModules_toSheafIso {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (SheafOfModules.toSheaf (integerRingSheaf X)).obj
        (abelianSheaf_integerModules F) ≅ F :=
  (sheafificationIso F).symm

/-- The comparison `abelianSheaf_integerModules_toSheafIso` is the inverse of
`sheafificationIso`. -/
theorem abelianSheaf_integerModules_toSheafIso_hom {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (abelianSheaf_integerModules_toSheafIso F).hom = (sheafificationIso F).inv :=
  sorry

/-- The sheaf of `ℤ̲_X`-modules `f_! ℤ̲`, the constant-integer module structure on
abelian extension by zero of `ℤ̲_U`. -/
noncomputable def extensionByZeroInteger {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    SheafOfModules.{u + 1} (integerRingSheaf X) :=
  abelianSheaf_integerModules
    ((abelianExtensionByZero f).obj (constantIntegerSheaf U))

/-- `extensionByZeroInteger f` is the integer-module structure on
`f_! ℤ̲_U`. -/
theorem extensionByZeroInteger_def {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    extensionByZeroInteger f =
      abelianSheaf_integerModules
        ((abelianExtensionByZero f).obj (constantIntegerSheaf U)) :=
  sorry

/-- The underlying abelian sheaf of the module `f_! ℤ̲` is abelian extension by
zero of `ℤ̲_U`. -/
noncomputable def extensionByZeroInteger_toSheafIso {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    (SheafOfModules.toSheaf (integerRingSheaf X)).obj (extensionByZeroInteger f) ≅
      (abelianExtensionByZero f).obj (constantIntegerSheaf U) :=
  abelianSheaf_integerModules_toSheafIso
    ((abelianExtensionByZero f).obj (constantIntegerSheaf U))

/-- The comparison `extensionByZeroInteger_toSheafIso` is the sheafification counit
on abelian `f_! ℤ̲`. -/
theorem extensionByZeroInteger_toSheafIso_hom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    (extensionByZeroInteger_toSheafIso f).hom =
      (abelianSheaf_integerModules_toSheafIso
          ((abelianExtensionByZero f).obj (constantIntegerSheaf U))).hom :=
  sorry

/-- The structure module `ℤ̲_X` forgets to the constant integer sheaf. -/
noncomputable def unitAbelianIso (X : AlgebraicSpace S) :
    (SheafOfModules.toSheaf (integerRingSheaf X)).obj
        (SheafOfModules.unit (integerRingSheaf X)) ≅ constantIntegerSheaf X :=
  (sheafCompose (smallEtaleTopology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapIso
      (integerRingSheafIsoConstant X) ≪≫
    (constantCommuteCompose (smallEtaleTopology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).app
      (RingCat.of (ULift.{u + 1} ℤ))

/-- `unitAbelianIso` is coefficient change of `integerRingSheafIsoConstant` followed
by `constantCommuteCompose`. -/
theorem unitAbelianIso_hom (X : AlgebraicSpace S) :
    (unitAbelianIso X).hom =
      ((sheafCompose (smallEtaleTopology X)
            (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapIso
          (integerRingSheafIsoConstant X) ≪≫
        (constantCommuteCompose (smallEtaleTopology X)
            (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).app
          (RingCat.of (ULift.{u + 1} ℤ))).hom :=
  sorry

/-- The trace `Tr_f` as a morphism of `ℤ̲_X`-modules, the unique module map whose
underlying abelian sheaf map is the adjunct of `constantIntegerPullbackHom`. -/
noncomputable def traceMapModule {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    extensionByZeroInteger f ⟶ SheafOfModules.unit (integerRingSheaf X) :=
  ⟨PresheafOfModules.homMk
      ((SheafOfModules.toSheafCompSheafToPresheafIso (integerRingSheaf X)).hom.app
          (extensionByZeroInteger f) ≫
        (extensionByZeroInteger_toSheafIso f).hom.hom ≫ (traceMap f).hom ≫
          (unitAbelianIso X).inv.hom ≫
            (SheafOfModules.toSheafCompSheafToPresheafIso
                (integerRingSheaf X)).inv.app
              (SheafOfModules.unit (integerRingSheaf X)))
      sorry⟩

/-- The underlying abelian sheaf map of the module-level trace is the actual
trace `Tr_f`, transported along the forgetful comparison isomorphisms. -/
theorem traceMapModule_toSheaf {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    (SheafOfModules.toSheaf (integerRingSheaf X)).map (traceMapModule f) =
      (extensionByZeroInteger_toSheafIso f).hom ≫
        traceMap f ≫ (unitAbelianIso X).inv :=
  sorry

/-- The module-level trace is the unique `ℤ̲`-linear lift of `Tr_f`. -/
theorem traceMapModule_spec {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    (SheafOfModules.toSheaf (integerRingSheaf X)).map (traceMapModule f) ≫
        (unitAbelianIso X).hom =
      (extensionByZeroInteger_toSheafIso f).hom ≫ traceMap f :=
  sorry

/-- The degree-`n + 1` exterior power `∧^{n+1} (f_! ℤ̲)` as a sheaf of
`ℤ̲`-modules. -/
noncomputable def koszulTerm {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] (n : ℕ) :
    ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X) (constantIntegerRingSheaf X) :=
  SheafOfModules.RingedSite.ExteriorPower.sheaf
    (constantIntegerRingSheaf X) (extensionByZeroInteger f) (n + 1)

/-- The Koszul term in degree `n` is the exterior power `∧^{n+1} (f_! ℤ̲)`. -/
theorem koszulTerm_def {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] (n : ℕ) :
    koszulTerm f n =
      SheafOfModules.RingedSite.ExteriorPower.sheaf
        (constantIntegerRingSheaf X) (extensionByZeroInteger f) (n + 1) :=
  sorry

/-- The Koszul differential `∧^{n+2} (f_! ℤ̲) ⟶ ∧^{n+1} (f_! ℤ̲)` of the trace. -/
noncomputable def koszulDifferential {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] (n : ℕ) :
    SheafOfModules.RingedSite.ExteriorPower.sheaf
        (constantIntegerRingSheaf X) (extensionByZeroInteger f) (n + 2) ⟶
      SheafOfModules.RingedSite.ExteriorPower.sheaf
        (constantIntegerRingSheaf X) (extensionByZeroInteger f) (n + 1) :=
  SheafOfModules.RingedSite.Koszul.differential
    (constantIntegerRingSheaf X) (traceMapModule f) (n + 1)

/-- Consecutive truncated Koszul differentials compose to zero. -/
theorem koszulDifferential_sq {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] (n : ℕ) :
    koszulDifferential f (n + 1) ≫ koszulDifferential f n = 0 :=
  sorry

/-- The truncated Koszul complex of `Tr_f` as a chain complex of `ℤ̲`-modules, with
degree-`n` term `∧^{n+1} (f_! ℤ̲)`. -/
noncomputable def koszulComplexModules {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] :
    ChainComplex
      (ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (smallEtaleTopology X) (constantIntegerRingSheaf X)) ℕ :=
  ChainComplex.of
    (fun n ↦ SheafOfModules.RingedSite.ExteriorPower.sheaf
      (constantIntegerRingSheaf X) (extensionByZeroInteger f) (n + 1))
    (koszulDifferential f) (koszulDifferential_sq f)


/-- The degree-`n` term of the module-level truncated Koszul complex is
`∧^{n+1} (f_! ℤ̲)`. -/
theorem koszulComplexModules_X {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] (n : ℕ) :
    (koszulComplexModules f).X n =
      SheafOfModules.RingedSite.ExteriorPower.sheaf
        (constantIntegerRingSheaf X) (extensionByZeroInteger f) (n + 1) :=
  sorry

/-- The truncated Koszul complex `K^•(f)` as a chain complex of abelian sheaves on
`X_étale`, with `K^n = ∧^{n+1} (f_! ℤ̲)`. -/
noncomputable def koszulComplex {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] :
    ChainComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ℕ :=
  ((SheafOfModules.toSheaf (integerRingSheaf X)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (koszulComplexModules f)

/-- The degree-`n` term of `K^•(f)` is the underlying abelian sheaf of
`∧^{n+1} (f_! ℤ̲)`. -/
theorem koszulComplex_X {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] (n : ℕ) :
    (koszulComplex f).X n =
      (SheafOfModules.toSheaf (integerRingSheaf X)).obj (koszulTerm f n) :=
  sorry

/-- The differential `K^{n+1} ⟶ K^n` is the underlying abelian sheaf map of the
Koszul differential of `Tr_f`. -/
theorem koszulComplex_d {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] (n : ℕ) :
    (koszulComplex f).d (n + 1) n =
      (SheafOfModules.toSheaf (integerRingSheaf X)).map (koszulDifferential f n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
