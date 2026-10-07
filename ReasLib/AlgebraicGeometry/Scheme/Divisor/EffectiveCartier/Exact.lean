module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion.Exact

/-!
# Exact sequences of effective Cartier divisors

Regular sections of invertible module sheaves and effective Cartier divisors determine canonical
short exact sequences of module sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The section map of an invertible module sheaf followed by restriction to its zero scheme is
zero. -/
theorem zeroSchemeRestrictionSequence_comp
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) [RingedSpace.IsRegularSection ℒ s] :
    (ℒ.unitHomEquiv.symm s :
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ ℒ) ≫
      Scheme.Modules.ClosedImmersion.restrictionMap (zeroSchemeι ℒ s) ℒ = 0 := sorry

/-- The canonical restriction complex of an invertible module sheaf along the zero scheme of a
regular section. -/
noncomputable def zeroSchemeRestrictionSequence
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) [RingedSpace.IsRegularSection ℒ s] :
    ShortComplex X.Modules :=
  ShortComplex.mk
    (ℒ.unitHomEquiv.symm s :
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ ℒ)
    (Scheme.Modules.ClosedImmersion.restrictionMap (zeroSchemeι ℒ s) ℒ)
    (zeroSchemeRestrictionSequence_comp ℒ s)

/-- The canonical restriction complex of an invertible module sheaf along the zero scheme of a
regular section is short exact. -/
theorem zeroSchemeRestrictionSequence_shortExact
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) [RingedSpace.IsRegularSection ℒ s] :
    (zeroSchemeRestrictionSequence ℒ s).ShortExact := sorry

/-- Evaluation against a regular section followed by the structure-module quotient to its zero
scheme is zero. -/
theorem zeroSchemeStructureSheafSequence_comp
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) [RingedSpace.IsRegularSection ℒ s] :
    dualSectionHom ℒ s ≫
      SheafOfModules.unitToPushforwardObjUnit
        (zeroSchemeι ℒ s).toRingCatSheafHom = 0 := sorry

/-- The canonical structure-sheaf complex of the zero scheme of a regular section of an
invertible module sheaf. -/
noncomputable def zeroSchemeStructureSheafSequence
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) [RingedSpace.IsRegularSection ℒ s] :
    ShortComplex X.Modules :=
  ShortComplex.mk (dualSectionHom ℒ s)
    (SheafOfModules.unitToPushforwardObjUnit
      (zeroSchemeι ℒ s).toRingCatSheafHom)
    (zeroSchemeStructureSheafSequence_comp ℒ s)

/-- The canonical structure-sheaf complex of the zero scheme of a regular section of an
invertible module sheaf is short exact. -/
theorem zeroSchemeStructureSheafSequence_shortExact
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) [RingedSpace.IsRegularSection ℒ s] :
    (zeroSchemeStructureSheafSequence ℒ s).ShortExact := sorry

namespace IdealSheafData

/-- The restriction map from the sheaf associated to an effective Cartier divisor to the
pushforward of its normal sheaf. -/
noncomputable def normalRestrictionMap
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    D.associatedSheaf ⟶
      (Scheme.Modules.pushforward D.subschemeι).obj
        (Scheme.Hom.normalSheaf D.subschemeι) :=
  Scheme.Modules.ClosedImmersion.restrictionMap D.subschemeι D.associatedSheaf ≫
    (Scheme.Modules.pushforward D.subschemeι).map D.normalSheafIso.hom

/-- The canonical section of an effective Cartier divisor followed by restriction to its normal
sheaf is zero. -/
theorem normalSheafSequence_comp
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    (D.associatedSheaf.unitHomEquiv.symm D.canonicalSection :
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ D.associatedSheaf) ≫
      D.normalRestrictionMap = 0 := sorry

/-- The complex from the structure sheaf through the sheaf associated to an effective Cartier
divisor to the pushed-forward normal sheaf. -/
noncomputable def normalSheafSequence
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    ShortComplex X.Modules :=
  ShortComplex.mk
    (D.associatedSheaf.unitHomEquiv.symm D.canonicalSection :
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ D.associatedSheaf)
    D.normalRestrictionMap D.normalSheafSequence_comp

/-- The complex from the structure sheaf through the sheaf associated to an effective Cartier
divisor to the pushed-forward normal sheaf is short exact. -/
theorem normalSheafSequence_shortExact
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    D.normalSheafSequence.ShortExact := sorry

/-- The ideal inclusion and the structure-module quotient of an effective Cartier divisor form a
complex. -/
noncomputable def structureSheafSequence
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    ShortComplex X.Modules :=
  ShortComplex.mk D.toSubobject.arrow
    (SheafOfModules.unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom)
    D.toSubobject_arrow_comp_quotient

/-- The ideal-to-structure-sheaf complex of an effective Cartier divisor is short exact. -/
theorem structureSheafSequence_shortExact
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    D.structureSheafSequence.ShortExact := sorry

end IdealSheafData

end AlgebraicGeometry.Scheme
