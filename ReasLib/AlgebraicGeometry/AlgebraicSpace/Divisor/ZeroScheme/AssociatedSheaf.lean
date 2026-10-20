module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.AssociatedSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.ZeroScheme

/-!
# Associated sheaves and zero schemes on algebraic spaces

Effective Cartier divisors have regular canonical sections. A regular section
recovers its invertible sheaf by a unique section-preserving isomorphism, and
the canonical section recovers the divisor ideal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical section of the sheaf associated to an effective Cartier divisor
is regular. -/
@[instance]
theorem canonicalSection_isRegular {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] :
    IsRegularSection (Hom.associatedSheaf i) (Hom.canonicalSection i) :=
  sorry

/-- A regular section of an invertible sheaf determines a unique isomorphism from
the sheaf associated to its zero scheme, carrying the canonical section to the
given section. -/
theorem existsUnique_associatedSheafIso_zeroScheme {S : Scheme.{u}}
    {X : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) [IsRegularSection L s] :
    ∃! e : Hom.associatedSheaf (zeroSchemeι L s) ≅ L,
      SheafOfModules.sectionsMap e.hom
        (Hom.canonicalSection (zeroSchemeι L s)) = s :=
  sorry

/-- The zero ideal of the canonical section of the sheaf associated to an
effective Cartier divisor is the ideal sheaf of that divisor. -/
theorem zeroIdealSubobject_associatedSheaf_canonicalSection {S : Scheme.{u}}
    {X : AlgebraicSpace S} (D : ClosedSubspace X)
    [IsEffectiveCartierDivisor D.ι] :
    zeroIdealSubobject D.associatedSheaf D.canonicalSection = D.idealSheaf :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
