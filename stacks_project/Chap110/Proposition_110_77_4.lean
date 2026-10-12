/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap110.Proposition_110_77_2

/-!
# Serre quotient of abelian groups by torsion

The induced localization functor of Proposition 110.77.2 at `R = ℤ`, composed with
restriction of scalars along `FractionRing.algEquiv ℤ ℚ : FractionRing ℤ ≃ₐ[ℤ] ℚ`,
identifies the Serre quotient of `ModuleCat ℤ` by torsion with `ModuleCat ℚ`.
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

/-- Proposition 110.77.4: the quotient of the category of abelian groups modulo its
Serre subcategory of torsion groups is the category of ℚ-vector spaces.

Identifying abelian groups with `ModuleCat ℤ` via `forget₂ (ModuleCat ℤ) AddCommGrpCat`,
and torsion groups with `isTorsion` at `ℤ`, this is the equivalence of
`inducedLocalizedFunctorRat` with `ModuleCat ℚ`. -/
@[stacks 0B0M]
theorem inducedLocalizedFunctorRat_isEquivalence :
    inducedLocalizedFunctorRat.IsEquivalence :=
  sorry

end ModuleCat
