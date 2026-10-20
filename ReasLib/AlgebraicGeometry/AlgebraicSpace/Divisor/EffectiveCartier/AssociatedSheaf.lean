/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.EffectiveCartier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.StructureModule
public import ReasLib.CategoryTheory.Monoidal.Invertible.Duality
public import ReasLib.CategoryTheory.Monoidal.Duality.Adjunction

/-! # Sheaves associated to effective Cartier divisors

An invertible ideal determines its tensor inverse, the canonical section dual to
its inclusion, and the negative and difference sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.MonoidalCategory.isInvertibleObject
  (inverse tensorInverseIso inverseTensorIso inverseIsInvertible)
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IdealSubobject

/-- The sheaf associated to an invertible ideal is the tensor inverse of its
underlying module. -/
noncomputable abbrev associatedSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] : X.Modules :=
  inverse I.toModule

/-- The associated sheaf is definitionally the tensor inverse of the ideal sheaf. -/
theorem associatedSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    associatedSheaf I = inverse I.toModule :=
  rfl

/-- Duality identifies maps from the structure module to the associated sheaf
with maps from the ideal module to the structure module. -/
noncomputable def canonicalSectionHomEquiv {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    (SheafOfModules.unit (structureSheaf X) ⟶ associatedSheaf I) ≃
      (I.toModule ⟶ SheafOfModules.unit (structureSheaf X)) :=
  (((structureModuleIsoTensorUnit X).homCongr (λ_ (associatedSheaf I)).symm).trans
    ((CategoryTheory.MonoidalCategory.isInvertibleObject.exactPairing I.toModule).unitHomEquiv
      (𝟙_ X.Modules))).trans
    ((Iso.refl I.toModule).homCongr (structureModuleIsoTensorUnit X).symm)

/-- The canonical morphism into the associated sheaf corresponds under duality to
the inclusion of the ideal into the structure module. -/
noncomputable def canonicalSectionHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    SheafOfModules.unit (structureSheaf X) ⟶ associatedSheaf I :=
  (canonicalSectionHomEquiv I).symm I.arrow

/-- Duality sends the canonical section morphism to the ideal inclusion. -/
theorem canonicalSectionHom_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    canonicalSectionHomEquiv I (canonicalSectionHom I) = I.arrow :=
  (canonicalSectionHomEquiv I).apply_symm_apply I.arrow

/-- The canonical global section of `𝒪_X(D)` corresponding to the inclusion `I_D ⟶ 𝒪_X`. -/
noncomputable def canonicalSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    (associatedSheaf I).sections :=
  (associatedSheaf I).unitHomEquiv (canonicalSectionHom I)

/-- Recovering the canonical section morphism from the canonical global section. -/
theorem canonicalSection_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    (associatedSheaf I).unitHomEquiv.symm (canonicalSection I) = canonicalSectionHom I :=
  (associatedSheaf I).unitHomEquiv.symm_apply_apply (canonicalSectionHom I)

/-- The negative-divisor sheaf attached to an invertible ideal sheaf is the ideal sheaf
itself. -/
noncomputable abbrev negSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] : X.Modules :=
  I.toModule

/-- The negative-divisor sheaf is definitionally the underlying module of the ideal sheaf. -/
theorem negSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    negSheaf I = I.toModule :=
  rfl

/-- The tensor product of `𝒪_X(D)` with `I_D` is canonically the monoidal unit. -/
noncomputable def associatedSheafTensorNegIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    associatedSheaf I ⊗ negSheaf I ≅ 𝟙_ X.Modules :=
  inverseTensorIso I.toModule

/-- The pairing `𝒪_X(D) ⊗ I_D ≅ 𝟙` is the tensor-inverse comparison of `I_D`. -/
theorem associatedSheafTensorNegIso_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [isInvertibleObject I.toModule] :
    associatedSheafTensorNegIso I = inverseTensorIso I.toModule :=
  rfl

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
  rfl

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
  rfl

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
  rfl

/-- The canonical global section `1_D` of `𝒪_X(D)`. -/
noncomputable abbrev canonicalSection {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] : (associatedSheaf i).sections :=
  IdealSubobject.canonicalSection (idealSheafSubobject i)

/-- The canonical section of an effective Cartier divisor is the canonical section of its
ideal sheaf. -/
theorem canonicalSection_eq {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] :
    canonicalSection i = IdealSubobject.canonicalSection (idealSheafSubobject i) :=
  rfl

/-- The negative sheaf `𝒪_X(-D)` of an effective Cartier divisor is its ideal sheaf. -/
noncomputable abbrev negSheaf {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] : X.Modules :=
  idealSheaf i

/-- The negative sheaf of an effective Cartier divisor is definitionally its ideal sheaf. -/
theorem negSheaf_eq {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] :
    negSheaf i = idealSheaf i :=
  rfl

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
  rfl

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
  rfl

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
  rfl

/-- The unit morphism corresponding to the canonical section `1_D` of
`associatedSheaf D`, obtained by comparing `IdealSubobject.canonicalSectionHom`
along the structure-module isomorphism with the monoidal unit. -/
noncomputable def canonicalSectionHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] :
    𝟙_ X.Modules ⟶ associatedSheaf D :=
  (Modules.structureModuleIsoTensorUnit X).inv ≫
    IdealSubobject.canonicalSectionHom D.idealSheaf

/-- Comparing `canonicalSectionHom` along the structure-module isomorphism recovers
the canonical global section `1_D`. -/
theorem unitHomEquiv_canonicalSectionHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] :
    (associatedSheaf D).unitHomEquiv
        ((Modules.structureModuleIsoTensorUnit X).hom ≫ canonicalSectionHom D) =
      canonicalSection D :=
  sorry

/-- The negative sheaf of a closed subspace that is an effective Cartier divisor. -/
noncomputable abbrev negSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsEffectiveCartierDivisor Z.ι] : X.Modules :=
  Hom.negSheaf Z.ι

/-- The negative sheaf of a closed subspace is the negative sheaf of its inclusion. -/
theorem negSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsEffectiveCartierDivisor Z.ι] :
    negSheaf Z = Hom.negSheaf Z.ι :=
  rfl

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
  rfl

end ClosedSubspace

/-- The difference sheaf `𝒪_X(D - D')` is isomorphic to
`𝒪_X(D) ⊗ 𝒪_X(D')^{⊗ -1}`. -/
theorem differenceSheaf_iso_tensor_inverse {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D D' : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι]
    [IsEffectiveCartierDivisor D'.ι] :
    Nonempty
      (ClosedSubspace.differenceSheaf D D' ≅
        ClosedSubspace.associatedSheaf D ⊗
          inverse (ClosedSubspace.associatedSheaf D')) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
