module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.ZeroScheme.AssociatedSheaf
import StacksCheckRecall

/-!
# Lemma 71.7.8

The canonical section of `𝒪_X(D)` is regular, a regular section of an invertible
sheaf determines a unique isomorphism from `𝒪_X(Z(s))`, and these constructions
are mutually inverse on ideal sheaves. The ideal identity expresses recovery of
the divisor up to isomorphism over `X`. For a regular section, `zeroScheme` is
effective Cartier by the imported regular-section criterion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.7.8: the canonical section of an effective Cartier divisor is
regular, and regular sections recover their sheaves and divisor ideals. -/
@[stacks 0847] #check
  (AlgebraicGeometry.AlgebraicSpace.canonicalSection_isRegular :
    ∀ {S : Scheme.{u}} {D X : AlgebraicSpace S} (i : D ⟶ X)
      [IsEffectiveCartierDivisor i],
      IsRegularSection (Hom.associatedSheaf i) (Hom.canonicalSection i))

#check
  (AlgebraicGeometry.AlgebraicSpace.existsUnique_associatedSheafIso_zeroScheme :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules)
      [isInvertibleObject L] (s : L.sections) [IsRegularSection L s],
      ∃! e : Hom.associatedSheaf (zeroSchemeι L s) ≅ L,
        SheafOfModules.sectionsMap e.hom
          (Hom.canonicalSection (zeroSchemeι L s)) = s)

#check
  (AlgebraicGeometry.AlgebraicSpace.zeroIdealSubobject_associatedSheaf_canonicalSection :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (D : ClosedSubspace X)
      [IsEffectiveCartierDivisor D.ι],
      zeroIdealSubobject D.associatedSheaf D.canonicalSection = D.idealSheaf)
