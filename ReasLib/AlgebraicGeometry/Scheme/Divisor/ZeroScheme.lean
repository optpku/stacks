module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.RegularSection
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme

/-!
# Divisor properties of zero schemes

This file records local principality of zero schemes of sections of invertible module sheaves and
characterizes when they are effective Cartier divisors.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The zero scheme of a section of an invertible module sheaf is a locally principal closed
subscheme. -/
theorem zeroScheme_isLocallyPrincipalClosedSubscheme
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections) :
    IsLocallyPrincipalClosedSubscheme (zeroSchemeι ℒ s) := sorry

/-- The zero scheme of a section of an invertible module sheaf is an effective Cartier divisor
exactly when the section is regular. -/
theorem zeroScheme_isEffectiveCartierDivisor_iff_isRegularSection
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections) :
    IsEffectiveCartierDivisor (zeroSchemeι ℒ s) ↔
      RingedSpace.IsRegularSection ℒ s := sorry

/-- A regular section of an invertible module sheaf cuts out an effective Cartier divisor. -/
instance instIsEffectiveCartierDivisorZeroScheme
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    [RingedSpace.IsRegularSection ℒ s] :
    IsEffectiveCartierDivisor (zeroIdealSheaf ℒ s).subschemeι :=
  (zeroScheme_isEffectiveCartierDivisor_iff_isRegularSection ℒ s).mpr inferInstance

namespace IdealSheafData

/-- The canonical section of the associated sheaf of an effective Cartier divisor is regular. -/
theorem canonicalSection_isRegular
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    RingedSpace.IsRegularSection D.associatedSheaf D.canonicalSection := sorry

end IdealSheafData

/-- The associated sheaf of the zero divisor of a regular section is uniquely isomorphic to the
original invertible module sheaf by an isomorphism carrying the canonical section to the given
section. -/
theorem existsUnique_associatedSheafIso_zeroIdealSheaf
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    [RingedSpace.IsRegularSection ℒ s] :
    ∃! e : (zeroIdealSheaf ℒ s).associatedSheaf ≅ ℒ,
      SheafOfModules.sectionsMap e.hom (zeroIdealSheaf ℒ s).canonicalSection = s := sorry

namespace IdealSheafData

/-- Taking the zero divisor of the canonical section of an effective Cartier divisor recovers the
original ideal-sheaf datum. -/
theorem zeroIdealSheaf_associatedSheaf_canonicalSection
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    zeroIdealSheaf D.associatedSheaf D.canonicalSection = D := sorry

end IdealSheafData

end AlgebraicGeometry.Scheme
