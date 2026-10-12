/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Definition_71_7_1_AssociatedSheaf
public import stacks_project.Chap71.Lemma_71_7_7_Divisor

/-!
# Lemma 71.7.8

The canonical section of `𝒪_X(D)` is regular, a regular section of an invertible
sheaf determines a unique isomorphism from `𝒪_X(Z(s))`, and these constructions
are mutually inverse on ideal sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.7.8 (1): if `D ⊂ X` is an effective Cartier divisor, then the canonical
section `1_D` of `𝒪_X(D)` is regular. -/
@[stacks 0847, instance]
theorem canonicalSection_isRegular {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] :
    IsRegularSection D.associatedSheaf D.canonicalSection :=
  sorry

/-- Lemma 71.7.8 (2): if `s` is a regular section of an invertible sheaf `ℒ`, then
there is a unique isomorphism `𝒪_X(Z(s)) ≅ ℒ` sending `1_Z(s)` to `s`. -/
@[stacks 0847]
theorem existsUnique_associatedSheafIso_zeroScheme {S : Scheme.{u}}
    {X : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) [IsRegularSection L s] :
    ∃! e : Hom.associatedSheaf (zeroSchemeι L s) ≅ L,
      SheafOfModules.sectionsMap e.hom
        (Hom.canonicalSection (zeroSchemeι L s)) = s :=
  sorry

/-- Lemma 71.7.8 (3): the constructions `D ↦ (𝒪_X(D), 1_D)` and `(ℒ, s) ↦ Z(s)`
are mutually inverse: the zero scheme of `1_D` recovers the ideal sheaf of `D`. -/
@[stacks 0847]
theorem zeroIdealSubobject_associatedSheaf_canonicalSection {S : Scheme.{u}}
    {X : AlgebraicSpace S} (D : ClosedSubspace X)
    [IsEffectiveCartierDivisor D.ι] :
    zeroIdealSubobject D.associatedSheaf D.canonicalSection = D.idealSheaf :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
