module

import ReasLib.AlgebraicGeometry.Scheme.Divisor.ZeroScheme
import StacksCheckRecall

/- Lemma 31.14.10 (1): the canonical section of the associated sheaf of an effective Cartier
divisor is regular. -/
@[stacks 01X0] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.canonicalSection_isRegular :
    ∀ {X : AlgebraicGeometry.Scheme} (D : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι],
      AlgebraicGeometry.RingedSpace.IsRegularSection D.associatedSheaf D.canonicalSection)

/- Lemma 31.14.10 (2): the zero scheme of a section of an invertible module sheaf is an
effective Cartier divisor exactly when the section is regular. -/
@[stacks 01X0] #check
  (AlgebraicGeometry.Scheme.zeroScheme_isEffectiveCartierDivisor_iff_isRegularSection :
    ∀ {X : AlgebraicGeometry.Scheme} (ℒ : X.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible ℒ] (s : ℒ.sections),
      AlgebraicGeometry.IsEffectiveCartierDivisor
          (AlgebraicGeometry.Scheme.zeroSchemeι ℒ s) ↔
        AlgebraicGeometry.RingedSpace.IsRegularSection ℒ s)

/- Lemma 31.14.10 (3): a regular section of an invertible module sheaf determines a unique
isomorphism from the associated sheaf of its zero divisor to the original module sheaf, carrying
the canonical section to the given section. -/
@[stacks 01X0] #check
  (AlgebraicGeometry.Scheme.existsUnique_associatedSheafIso_zeroIdealSheaf :
    ∀ {X : AlgebraicGeometry.Scheme} (ℒ : X.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
      [AlgebraicGeometry.RingedSpace.IsRegularSection ℒ s],
      ∃! e : (AlgebraicGeometry.Scheme.zeroIdealSheaf ℒ s).associatedSheaf ≅ ℒ,
        SheafOfModules.sectionsMap e.hom
            (AlgebraicGeometry.Scheme.zeroIdealSheaf ℒ s).canonicalSection = s)

/- Lemma 31.14.10 (4): taking the zero divisor of the canonical section of an effective Cartier
divisor recovers the original ideal-sheaf datum. -/
@[stacks 01X0] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.zeroIdealSheaf_associatedSheaf_canonicalSection :
    ∀ {X : AlgebraicGeometry.Scheme} (D : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι],
      AlgebraicGeometry.Scheme.zeroIdealSheaf D.associatedSheaf D.canonicalSection = D)
