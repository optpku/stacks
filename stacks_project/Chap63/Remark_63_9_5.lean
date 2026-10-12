/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Remark_63_9_5_Comparison
import StacksCheckRecall

/-!
# Derived étale comparison `Rf_! ⟶ Rf_*`

A separated finite-type morphism of schemes with quasi-compact
quasi-separated target induces a functorial comparison
`Rf_! K ⟶ Rf_* K` on `D⁺_tors(X_étale, Λ)`, and on all of
`D(X_étale, Λ)` when `Λ` is torsion, compatible with composition and
base change.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Etale

/- Remark 63.9.5 (1): Let `f : X ⟶ Y` be a finite type separated morphism of
schemes with `Y` quasi-compact and quasi-separated. There is a functorial
comparison `Rf_! K ⟶ Rf_* K` on objects of `D⁺_tors(X_étale, Λ)`, or of
`D(X_étale, Λ)` if `Λ` is torsion, constructed from a compactification
`j : X ⟶ X̄` over `Y` by promoting `j_! ⟶ j_*` of Lemma 59.70.6. -/
@[stacks 0H6X]
#check AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.toPushforward

/- Remark 63.9.5 (2): this transformation is compatible with the isomorphism
`Rg_! ∘ Rf_! ⟶ R(g ∘ f)_!` of Lemma 63.9.2 and the isomorphism
`Rg_* ∘ Rf_* ⟶ R(g ∘ f)_*` of Cohomology on Sites, Lemma 21.19.2. -/
@[stacks 0H6X]
#check AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.toPushforward_comp_compat

/- Remark 63.9.5 (3): this transformation is compatible with the isomorphism
`g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of Lemma 63.9.4 and the base change map of
Cohomology on Sites, Remark 21.19.3. -/
@[stacks 0H6X]
#check AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.toPushforward_baseChange_compat

/- Remark 63.9.5 (4): the resulting transformation is independent of the
choice of compactification on objects of `D⁺_tors(X_étale, Λ)`. -/
@[stacks 0H6X]
#check AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.toPushforward_isoOfHom_of_isGE_isTorsion

/- Remark 63.9.5 (5): if `Λ` is torsion, the resulting transformation is
independent of the compactification as a natural transformation on
`D(X_étale, Λ)`. -/
@[stacks 0H6X]
#check AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.toPushforward_isoOfHom_of_isTorsion

end
