module

public import ReasLib.Algebra.Category.ModuleCat.Localization.SerreQuotient
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Rationalization of the Serre quotient by torsion

Localization of integer modules, followed by the canonical identification of
`FractionRing ℤ` with `ℚ`, identifies the Serre quotient by torsion with rational
vector spaces.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v

namespace ModuleCat

variable [Small.{v} ℤ]

/-- The induced localization functor of the Serre quotient of `ModuleCat ℤ` by torsion,
composed with restriction of scalars along the inverse of `FractionRing.algEquiv ℤ ℚ`,
landing in `ModuleCat ℚ`. -/
def inducedLocalizedFunctorRat :
    (isTorsion : ObjectProperty (ModuleCat.{v} ℤ)).isoModSerre.Localization ⥤
      ModuleCat.{v} ℚ :=
  inducedLocalizedFunctor (nonZeroDivisors ℤ) ⋙
    restrictScalars
      ((FractionRing.algEquiv ℤ ℚ : FractionRing ℤ ≃ₐ[ℤ] ℚ).toRingEquiv.symm.toRingHom)

/-- Restriction of scalars along `FractionRing.algEquiv ℤ ℚ`, then the Serre quotient of
`ModuleCat ℤ` by torsion. -/
def quotientRestrictScalarsRat :
    ModuleCat.{v} ℚ ⥤
      (isTorsion : ObjectProperty (ModuleCat.{v} ℤ)).isoModSerre.Localization :=
  restrictScalars
      ((FractionRing.algEquiv ℤ ℚ : FractionRing ℤ ≃ₐ[ℤ] ℚ).toRingEquiv.toRingHom) ⋙
    quotientRestrictScalars (nonZeroDivisors ℤ)

/-- Rationalization is an equivalence from the Serre quotient of integer modules by
torsion modules to the category of rational vector spaces. -/
@[stacks 0B0M]
theorem inducedLocalizedFunctorRat_isEquivalence :
    inducedLocalizedFunctorRat.IsEquivalence :=
  sorry

/-- Rationalization of the Serre quotient of integer modules by torsion is canonically
an equivalence. -/
instance instIsEquivalenceInducedLocalizedFunctorRat :
    inducedLocalizedFunctorRat.IsEquivalence :=
  inducedLocalizedFunctorRat_isEquivalence

end ModuleCat
