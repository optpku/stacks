module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Ring.ULift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Constant
public import ReasLib.Algebra.Category.Ring.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ExtensionByZero

/-!
# Integer-module realizations of abelian sheaves on small étale sites

Abelian sheaves acquire their canonical constant-integer scalar action by
module sheafification. The étale trace is transported to a morphism of these
integer-module sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The constant sheaf of rings `ℤ̲` on the small étale site of an algebraic space. -/
noncomputable abbrev constantIntegerRingSheaf (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  (constantSheaf (smallEtaleTopology X) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} ℤ))

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

/-- The ring-sheaf morphism `ℤ̲_U ⟶ f⁻¹ ℤ̲_X` obtained by applying coefficient
change to the constant integer comparison. -/
noncomputable def constantIntegerRingRestrictionHom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf U) ⟶
      (etaleRestrictionSheaf f RingCat.{u + 1}).obj (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X)) :=
  (sheafCompose (smallEtaleTopology U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (constantIntegerRingPullbackHom f)

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
    CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X) ≅
      (constantSheaf (smallEtaleTopology X) RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1} ℤ)) :=
  (constantCommuteCompose (smallEtaleTopology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
    (CommRingCat.of (ULift.{u + 1} ℤ))

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

/-- The constant integer ring presheaf maps to the underlying ring sheaf of the
constant commutative integer sheaf by its sheafification comparison. -/
noncomputable def constantIntegerRingPresheafToSheaf (X : AlgebraicSpace S) :
    (Functor.const (smallEtaleSite X)ᵒᵖ).obj (RingCat.of (ULift.{u + 1} ℤ)) ⟶
      (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X)).obj :=
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
    SheafOfModules.{u + 1} (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X)) :=
  (PresheafOfModules.sheafification (constantIntegerRingPresheafToSheaf X)).obj
    (abelianSheaf_constantIntegerPresheaf F)

/-- The underlying abelian sheaf of `abelianSheaf_integerModules F` is `F`. -/
noncomputable def abelianSheaf_integerModules_toSheafIso {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X))).obj
        (abelianSheaf_integerModules F) ≅ F :=
  (sheafificationIso F).symm

/-- The sheaf of `ℤ̲_X`-modules `f_! ℤ̲`, the constant-integer module structure on
abelian extension by zero of `ℤ̲_U`. -/
noncomputable def extensionByZeroInteger {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    SheafOfModules.{u + 1} (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X)) :=
  abelianSheaf_integerModules
    ((abelianExtensionByZero f).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology U)))

/-- The underlying abelian sheaf of the module `f_! ℤ̲` is abelian extension by
zero of `ℤ̲_U`. -/
noncomputable def extensionByZeroInteger_toSheafIso {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X))).obj (extensionByZeroInteger f) ≅
      (abelianExtensionByZero f).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology U)) :=
  abelianSheaf_integerModules_toSheafIso
    ((abelianExtensionByZero f).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology U)))

/-- The structure module `ℤ̲_X` forgets to the constant integer sheaf. -/
noncomputable def unitAbelianIso (X : AlgebraicSpace S) :
    (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X))).obj
        (SheafOfModules.unit (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X))) ≅ CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X) :=
  (sheafCompose (smallEtaleTopology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapIso
      (integerRingSheafIsoConstant X) ≪≫
    (constantCommuteCompose (smallEtaleTopology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).app
      (RingCat.of (ULift.{u + 1} ℤ))

/-- The trace `Tr_f` as a morphism of `ℤ̲_X`-modules, the unique module map whose
underlying abelian sheaf map is the adjunct of `constantIntegerPullbackHom`. -/
noncomputable def traceMapModule {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    extensionByZeroInteger f ⟶ SheafOfModules.unit (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X)) :=
  ⟨PresheafOfModules.homMk
      ((SheafOfModules.toSheafCompSheafToPresheafIso (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X))).hom.app
          (extensionByZeroInteger f) ≫
        (extensionByZeroInteger_toSheafIso f).hom.hom ≫ (traceMap f).hom ≫
          (unitAbelianIso X).inv.hom ≫
            (SheafOfModules.toSheafCompSheafToPresheafIso
                (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X))).inv.app
              (SheafOfModules.unit (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X))))
      sorry⟩

/-- The underlying abelian sheaf map of the module-level trace is the actual
trace `Tr_f`, transported along the forgetful comparison isomorphisms. -/
theorem traceMapModule_toSheaf {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X))).map (traceMapModule f) =
      (extensionByZeroInteger_toSheafIso f).hom ≫
        traceMap f ≫ (unitAbelianIso X).inv :=
  sorry

/-- The module-level trace is the unique `ℤ̲`-linear lift of `Tr_f`. -/
theorem traceMapModule_spec {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X))).map (traceMapModule f) ≫
        (unitAbelianIso X).hom =
      (extensionByZeroInteger_toSheafIso f).hom ≫ traceMap f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
