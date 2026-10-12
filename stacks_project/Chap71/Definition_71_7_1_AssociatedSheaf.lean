/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier

/-!
# Invertible sheaves associated to effective Cartier divisors

An effective Cartier divisor `D ⊂ X` on an algebraic space has an invertible ideal
sheaf `I_D`. This module records the associated invertible sheaf
`𝒪_X(D) = Hom_{𝒪_X}(I_D, 𝒪_X) = I_D^{⊗ -1}`, its canonical section corresponding to
`I_D ⟶ 𝒪_X`, the negative sheaf `𝒪_X(-D) = I_D`, and the difference sheaf
`𝒪_X(D - D') = 𝒪_X(D) ⊗ 𝒪_X(-D')`.

The sheaf Hom is the local-Hom object `Modules.internalHom` on the universe-lifted
commutative presentation, where `InternalHom.moduleMonoidalClosed` applies. On
`X.Modules` the associated sheaf is the tensor inverse of `I_D`, identified with
that local Hom after `liftModule`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.MonoidalCategory.isInvertibleObject
  (inverse tensorInverseIso inverseTensorIso inverseIsInvertible)
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.InternalHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

/-- A morphism of commutative `𝒪_X`-modules lifts on sections over `U` by universe-lifting
the component at `U`. -/
noncomputable def liftedSectionMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : commModules X} (f : F ⟶ G) (U : (smallEtaleSite X)ᵒᵖ) :
    liftedSection F U ⟶ liftedSection G U :=
  eqToHom (liftedSection_eq F U).symm ≫
    (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).map
      ((ModuleCat.uliftFunctor.{u + 1, u} ((commStructureSheaf X).obj.obj U)).map
        (f.val.app U)) ≫
    eqToHom (liftedSection_eq G U)

/-- `liftedSectionMap` is restriction of scalars of the universe lift of the component
at `U`. -/
theorem liftedSectionMap_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : commModules X} (f : F ⟶ G) (U : (smallEtaleSite X)ᵒᵖ) :
    liftedSectionMap f U =
      eqToHom (liftedSection_eq F U).symm ≫
        (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).map
          ((ModuleCat.uliftFunctor.{u + 1, u} ((commStructureSheaf X).obj.obj U)).map
            (f.val.app U)) ≫
        eqToHom (liftedSection_eq G U) :=
  sorry

/-- A morphism of commutative `𝒪_X`-modules lifts to the universe-lifted presentation by
applying `ULift` sectionwise. -/
noncomputable def liftCommModuleMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : commModules X} (f : F ⟶ G) :
    liftCommModule F ⟶ liftCommModule G where
  val :=
    { app := fun U ↦ liftedSectionMap f U
      naturality := sorry }

/-- The underlying natural transformation of `liftCommModuleMap` is `liftedSectionMap`. -/
theorem liftCommModuleMap_val_app {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : commModules X} (f : F ⟶ G) (U : (smallEtaleSite X)ᵒᵖ) :
    (liftCommModuleMap f).val.app U = liftedSectionMap f U :=
  sorry

/-- A morphism of `𝒪_X`-modules lifts to the universe-lifted commutative presentation. -/
noncomputable def liftModuleMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : X.Modules} (f : F ⟶ G) :
    liftModule F ⟶ liftModule G :=
  liftCommModuleMap ((toCommModules X).map f)

/-- `liftModuleMap` is `liftCommModuleMap` of the commutative presentation of `f`. -/
theorem liftModuleMap_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : X.Modules} (f : F ⟶ G) :
    liftModuleMap f = liftCommModuleMap ((toCommModules X).map f) :=
  sorry

/-- The universe lift of the structure module is the tensor unit of the lifted commutative
presentation, on sections. -/
noncomputable def liftedUnitIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    liftModule (SheafOfModules.unit (structureSheaf X)) ≅
      unitModule (smallEtaleTopology X) (commStructureSheafLift X) where
  hom :=
    { val :=
        { app := fun U ↦ 𝟙 _
          naturality := sorry } }
  inv :=
    { val :=
        { app := fun U ↦ 𝟙 _
          naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `liftedUnitIso` is the identity on sections. -/
theorem liftedUnitIso_hom_app {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (liftedUnitIso X).hom.val.app U = 𝟙 _ :=
  sorry

/-- Invertibility of an `𝒪_X`-module transports to its universe lift, where the local-Hom
closed structure is available. -/
instance instIsInvertibleObject_liftModule {S : Scheme.{u}} {X : AlgebraicSpace S}
    (M : X.Modules) [isInvertibleObject M] :
    isInvertibleObject (liftModule M) :=
  sorry

/-- Tensor-unit comparison on the universe-lifted commutative presentation of `𝒪_X`. -/
noncomputable def liftedUnitIsoTensorUnit {S : Scheme.{u}} (X : AlgebraicSpace S) :
    unitModule (smallEtaleTopology X) (commStructureSheafLift X) ≅
      𝟙_ (ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (smallEtaleTopology X) (commStructureSheafLift X)) :=
  unitIsoTensorUnit.{u + 1, u, u + 1}

/-- `liftedUnitIsoTensorUnit` is the ringed-site tensor-unit comparison on
`commStructureSheafLift X`. -/
theorem liftedUnitIsoTensorUnit_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    liftedUnitIsoTensorUnit X = unitIsoTensorUnit.{u + 1, u, u + 1} :=
  sorry

end Modules

namespace IdealSubobject

/-- The invertible sheaf associated to an invertible ideal sheaf is the tensor inverse of
`I_D` in `X.Modules`. After `liftModule`, this is the local Hom
`Hom_{𝒪_X}(I_D, 𝒪_X)` given by `Modules.internalHom`. -/
noncomputable abbrev associatedSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] : X.Modules :=
  inverse I.toModule

/-- The associated sheaf is definitionally the tensor inverse of the ideal sheaf. -/
theorem associatedSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    associatedSheaf I = inverse I.toModule :=
  sorry

/-- After universe lift, `I_D^{⊗ -1}` is the local Hom sheaf
`Hom_{𝒪_X}(I_D, 𝒪_X) = Modules.internalHom I_D 𝒪_X`, via `dual.isoOfTensorInverse`
for `InternalHom.moduleMonoidalClosed`. -/
noncomputable def associatedSheafIsoInternalHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    inverse (liftModule I.toModule) ≅
      internalHom I.toModule (SheafOfModules.unit (structureSheaf X)) :=
  dual.isoOfTensorInverse (liftModule I.toModule) (inverse (liftModule I.toModule))
      (tensorInverseIso (liftModule I.toModule) ≪≫
        (liftedUnitIsoTensorUnit X).symm) ≪≫
    (ihom (liftModule I.toModule)).mapIso (liftedUnitIso X).symm

/-- The comparison `I_D^{⊗ -1} ≅ Hom_{𝒪_X}(I_D, 𝒪_X)` after `liftModule` is the dual-to-inverse
isomorphism of local Hom, followed by the structure-module comparison. -/
theorem associatedSheafIsoInternalHom_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    (associatedSheafIsoInternalHom I).hom =
      (dual.isoOfTensorInverse (liftModule I.toModule)
          (inverse (liftModule I.toModule))
          (tensorInverseIso (liftModule I.toModule) ≪≫
            (liftedUnitIsoTensorUnit X).symm) ≪≫
        (ihom (liftModule I.toModule)).mapIso (liftedUnitIso X).symm).hom :=
  sorry

/-- The sheaf associated to an invertible ideal sheaf is tensor-invertible. -/
instance instIsInvertibleObject_associatedSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    isInvertibleObject (associatedSheaf I) :=
  inverseIsInvertible I.toModule

/-- The lifted canonical morphism `𝒪_X ⟶ Hom_{𝒪_X}(I_D, 𝒪_X)` is obtained by currying the
inclusion `I_D ⟶ 𝒪_X` with `InternalHom.homEquiv`. -/
noncomputable def canonicalSectionHomLifted {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    unitModule (smallEtaleTopology X) (commStructureSheafLift X) ⟶
      internalHom I.toModule (SheafOfModules.unit (structureSheaf X)) :=
  (liftedUnitIsoTensorUnit X).hom ≫
    homEquiv (commStructureSheafLift X) (liftModule I.toModule)
      (𝟙_ (ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (smallEtaleTopology X) (commStructureSheafLift X)))
      (liftModule (SheafOfModules.unit (structureSheaf X)))
      ((ρ_ (liftModule I.toModule)).hom ≫ liftModuleMap I.arrow)

/-- `canonicalSectionHomLifted` is the `InternalHom.homEquiv` curry of the lifted inclusion
`I_D ⟶ 𝒪_X`. -/
theorem canonicalSectionHomLifted_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    canonicalSectionHomLifted I =
      (liftedUnitIsoTensorUnit X).hom ≫
        homEquiv (commStructureSheafLift X) (liftModule I.toModule)
          (𝟙_ (ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
            (smallEtaleTopology X) (commStructureSheafLift X)))
          (liftModule (SheafOfModules.unit (structureSheaf X)))
          ((ρ_ (liftModule I.toModule)).hom ≫ liftModuleMap I.arrow) :=
  sorry

/-- The canonical morphism `𝒪_X ⟶ 𝒪_X(D)` is the transport of the lifted local-Hom curry of
the inclusion `I_D ⟶ 𝒪_X` along `associatedSheafIsoInternalHom`. -/
noncomputable def canonicalSectionHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    SheafOfModules.unit (structureSheaf X) ⟶ associatedSheaf I :=
  (structureModuleIsoTensorUnit X).hom ≫
    curry ((ρ_ I.toModule).hom ≫ I.arrow ≫ (structureModuleIsoTensorUnit X).hom)

/-- The canonical section morphism is the curry of the inclusion of the ideal sheaf into the
structure sheaf. After `liftModule` this is `canonicalSectionHomLifted`. -/
theorem canonicalSectionHom_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    canonicalSectionHom I =
      (structureModuleIsoTensorUnit X).hom ≫
        curry ((ρ_ I.toModule).hom ≫ I.arrow ≫ (structureModuleIsoTensorUnit X).hom) :=
  sorry

/-- The canonical global section of `𝒪_X(D)` corresponding to the inclusion `I_D ⟶ 𝒪_X`. -/
noncomputable def canonicalSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    (associatedSheaf I).sections :=
  (associatedSheaf I).unitHomEquiv (canonicalSectionHom I)

/-- Recovering the canonical section morphism from the canonical global section. -/
theorem canonicalSection_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    (associatedSheaf I).unitHomEquiv.symm (canonicalSection I) = canonicalSectionHom I :=
  sorry

/-- The negative-divisor sheaf attached to an invertible ideal sheaf is the ideal sheaf
itself. -/
noncomputable abbrev negSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] : X.Modules :=
  I.toModule

/-- The negative-divisor sheaf is definitionally the underlying module of the ideal sheaf. -/
theorem negSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    negSheaf I = I.toModule :=
  sorry

/-- The tensor product of `𝒪_X(D)` with `I_D` is canonically the monoidal unit. -/
noncomputable def associatedSheafTensorNegIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    associatedSheaf I ⊗ negSheaf I ≅ 𝟙_ X.Modules :=
  inverseTensorIso I.toModule

/-- The pairing `𝒪_X(D) ⊗ I_D ≅ 𝟙` is the tensor-inverse comparison of `I_D`. -/
theorem associatedSheafTensorNegIso_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    associatedSheafTensorNegIso I = inverseTensorIso I.toModule :=
  sorry

/-- The negative-divisor sheaf is the tensor inverse of the associated sheaf. -/
noncomputable def negSheafIsoInverseAssociatedSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    negSheaf I ≅ inverse (associatedSheaf I) :=
  (tensorLeft (associatedSheaf I)).asEquivalence.unitIso.app I.toModule ≪≫
    (tensorLeft (associatedSheaf I)).asEquivalence.inverse.mapIso
      (associatedSheafTensorNegIso I)

/-- The comparison `I_D ≅ 𝒪_X(D)^{⊗ -1}` is the unit of tensoring with `𝒪_X(D)`, followed by
the inverse of the pairing `𝒪_X(D) ⊗ I_D`. -/
theorem negSheafIsoInverseAssociatedSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    negSheafIsoInverseAssociatedSheaf I =
      (tensorLeft (associatedSheaf I)).asEquivalence.unitIso.app I.toModule ≪≫
        (tensorLeft (associatedSheaf I)).asEquivalence.inverse.mapIso
          (associatedSheafTensorNegIso I) :=
  sorry

/-- The sheaf associated to a difference of invertible ideal sheaves is the tensor product of
the positive associated sheaf with the negative-divisor sheaf. -/
noncomputable abbrev differenceSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I J : IdealSubobject X) [isInvertibleObject I.toModule]
    [isInvertibleObject J.toModule] : X.Modules :=
  associatedSheaf I ⊗ negSheaf J

/-- The difference sheaf is definitionally the tensor product of the positive associated sheaf
and the negative-divisor sheaf. -/
theorem differenceSheaf_def {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I J : IdealSubobject X) [isInvertibleObject I.toModule]
    [isInvertibleObject J.toModule] :
    differenceSheaf I J = associatedSheaf I ⊗ negSheaf J :=
  sorry

end IdealSubobject

namespace Hom

/-- The invertible sheaf `𝒪_X(D)` associated to an effective Cartier divisor. -/
noncomputable abbrev associatedSheaf {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] : X.Modules :=
  IdealSubobject.associatedSheaf (idealSheafSubobject i)

/-- The associated sheaf of an effective Cartier divisor is the associated sheaf of its
ideal sheaf. -/
theorem associatedSheaf_eq {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] :
    associatedSheaf i = IdealSubobject.associatedSheaf (idealSheafSubobject i) :=
  sorry

/-- The sheaf associated to an effective Cartier divisor is tensor-invertible. -/
instance instIsInvertibleObject_associatedSheaf {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] :
    isInvertibleObject (associatedSheaf i) :=
  inferInstance

/-- The canonical global section `1_D` of `𝒪_X(D)`. -/
noncomputable abbrev canonicalSection {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] : (associatedSheaf i).sections :=
  IdealSubobject.canonicalSection (idealSheafSubobject i)

/-- The canonical section of an effective Cartier divisor is the canonical section of its
ideal sheaf. -/
theorem canonicalSection_eq {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] :
    canonicalSection i = IdealSubobject.canonicalSection (idealSheafSubobject i) :=
  sorry

/-- The negative sheaf `𝒪_X(-D)` of an effective Cartier divisor is its ideal sheaf. -/
noncomputable abbrev negSheaf {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] : X.Modules :=
  idealSheaf i

/-- The negative sheaf of an effective Cartier divisor is definitionally its ideal sheaf. -/
theorem negSheaf_eq {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] :
    negSheaf i = idealSheaf i :=
  sorry

/-- The sheaf `𝒪_X(D - D')` associated to a difference of effective Cartier divisors. -/
noncomputable abbrev differenceSheaf {S : Scheme.{u}} {D D' X : AlgebraicSpace S}
    (i : D ⟶ X) (i' : D' ⟶ X) [IsEffectiveCartierDivisor i]
    [IsEffectiveCartierDivisor i'] : X.Modules :=
  associatedSheaf i ⊗ negSheaf i'

/-- The difference sheaf is the tensor product of `𝒪_X(D)` with `𝒪_X(-D')`. -/
theorem differenceSheaf_def {S : Scheme.{u}} {D D' X : AlgebraicSpace S}
    (i : D ⟶ X) (i' : D' ⟶ X) [IsEffectiveCartierDivisor i]
    [IsEffectiveCartierDivisor i'] :
    differenceSheaf i i' = associatedSheaf i ⊗ negSheaf i' :=
  sorry

end Hom

namespace ClosedSubspace

/-- The invertible sheaf associated to a closed subspace that is an effective Cartier
divisor. -/
noncomputable abbrev associatedSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsEffectiveCartierDivisor Z.ι] : X.Modules :=
  Hom.associatedSheaf Z.ι

/-- The associated sheaf of a closed subspace is the associated sheaf of its inclusion. -/
theorem associatedSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsEffectiveCartierDivisor Z.ι] :
    associatedSheaf Z = Hom.associatedSheaf Z.ι :=
  sorry

/-- The canonical global section of the sheaf associated to a closed subspace that is an
effective Cartier divisor. -/
noncomputable abbrev canonicalSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsEffectiveCartierDivisor Z.ι] :
    (associatedSheaf Z).sections :=
  Hom.canonicalSection Z.ι

/-- The canonical section of a closed subspace is the canonical section of its inclusion. -/
theorem canonicalSection_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsEffectiveCartierDivisor Z.ι] :
    canonicalSection Z = Hom.canonicalSection Z.ι :=
  sorry

/-- The negative sheaf of a closed subspace that is an effective Cartier divisor. -/
noncomputable abbrev negSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsEffectiveCartierDivisor Z.ι] : X.Modules :=
  Hom.negSheaf Z.ι

/-- The negative sheaf of a closed subspace is the negative sheaf of its inclusion. -/
theorem negSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsEffectiveCartierDivisor Z.ι] :
    negSheaf Z = Hom.negSheaf Z.ι :=
  sorry

/-- The difference sheaf associated to a pair of closed subspaces that are effective Cartier
divisors. -/
noncomputable abbrev differenceSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z Z' : ClosedSubspace X) [IsEffectiveCartierDivisor Z.ι]
    [IsEffectiveCartierDivisor Z'.ι] : X.Modules :=
  Hom.differenceSheaf Z.ι Z'.ι

/-- The difference sheaf of closed subspaces is the difference sheaf of their inclusions. -/
theorem differenceSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z Z' : ClosedSubspace X) [IsEffectiveCartierDivisor Z.ι]
    [IsEffectiveCartierDivisor Z'.ι] :
    differenceSheaf Z Z' = Hom.differenceSheaf Z.ι Z'.ι :=
  sorry

end ClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
