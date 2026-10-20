module

public import Mathlib.RingTheory.Nakayama
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.LocalizedModule.Submodule
public import ReasLib.LinearAlgebra.QuotientByIdeal

@[expose] public section

/-!
# Basic Nakayama criteria

This leaf owns the quotient-map, submodule, and Jacobson/nilpotent forms of
Nakayama's lemma.  Localization criteria live in the sibling
`ReasLib.RingTheory.Ideal.Nakayama.Localization` leaf.
-/

universe u v w

open scoped Pointwise

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- A map into a finite module is surjective when its map modulo an ideal is surjective and the
ideal lies in the Jacobson radical. -/
@[stacks 00DV "Nakayama surjectivity modulo a Jacobson-radical ideal"]
theorem surjective_of_quotientMapByIdeal_surjective_of_le_jacobson
    (f : N →ₗ[R] M) (I : Ideal R) [Module.Finite R M]
    (hquot : Function.Surjective (f.quotientMapByIdeal I))
    (hIjac : I ≤ Ring.jacobson R) : Function.Surjective f := sorry

/-- A map is surjective when its map modulo a nilpotent ideal is surjective. -/
@[stacks 00DV "Nakayama surjectivity modulo a nilpotent ideal"]
theorem surjective_of_quotientMapByIdeal_surjective_of_isNilpotent
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : N →ₗ[R] M) (I : Ideal R) (hquot : Function.Surjective (f.quotientMapByIdeal I))
    (hI : IsNilpotent I) : Function.Surjective f := sorry

/-- If a map into a finite module is surjective modulo an ideal, then it becomes surjective after
localizing away from some element congruent to `1` modulo that ideal. -/
@[stacks 00DV "Nakayama localized surjectivity"]
theorem exists_localizedAway_surjective
    (f : N →ₗ[R] M) (I : Ideal R) [Module.Finite R M]
    (hquot : Function.Surjective (f.quotientMapByIdeal I)) :
    ∃ r : R,
      r - 1 ∈ I ∧ Function.Surjective ((LocalizedModule.map (Submonoid.powers r)) f) := sorry

end LinearMap

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A finite module is subsingleton if multiplication by an ideal in the Jacobson radical already
generates the whole module. -/
@[stacks 00DV "Nakayama subsingleton criterion"]
theorem subsingleton_of_smul_top_eq_top_of_le_jacobson
    (I : Ideal R) [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) = ⊤)
    (hIjac : I ≤ Ring.jacobson R) : Subsingleton M := sorry

/-- A module is subsingleton if multiplication by a nilpotent ideal already generates the whole
module. -/
@[stacks 00DV "nilpotent Nakayama subsingleton criterion"]
theorem subsingleton_of_smul_top_eq_top_of_isNilpotent
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (hIM : I • (⊤ : Submodule R M) = ⊤)
    (hI : IsNilpotent I) : Subsingleton M := sorry

end Module

namespace Submodule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- If a submodule together with an ideal multiple of a finitely generated submodule generates
the ambient module, then it generates after localizing away from an element congruent to `1`
modulo that ideal. The returned element also sends the whole module into the original submodule. -/
@[stacks 00DV "Nakayama localized submodule generation"]
theorem exists_sub_one_mem_and_smul_top_le_of_sup_eq_top
    {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG) (hMN : N ⊔ I • N' = ⊤) :
    ∃ r : R,
      r - 1 ∈ I ∧ r • (⊤ : Submodule R M) ≤ N ∧ N.localized (Submonoid.powers r) = ⊤ := sorry

/-- If a submodule generates a finite module after quotienting by an ideal, then it generates
after localizing away from an element congruent to `1` modulo that ideal. The returned element
also sends the whole module into the original submodule. -/
@[stacks 00DV "Nakayama localized quotient-submodule generation"]
theorem exists_sub_one_mem_and_localized_eq_top_of_quotient_eq_top
    {I : Ideal R} {N : Submodule R M} [Module.Finite R M]
    (hgen : Submodule.map (I • (⊤ : Submodule R M)).mkQ N = ⊤) :
    ∃ r : R,
      r - 1 ∈ I ∧ r • (⊤ : Submodule R M) ≤ N ∧ N.localized (Submonoid.powers r) = ⊤ := sorry

/-- If a family generates a finite module modulo an ideal, then its span admits both a
clearing-scalar inclusion and generation after localizing away from an element congruent to `1`
modulo that ideal. -/
@[stacks 00DV "Nakayama localized quotient-span generation"]
theorem exists_sub_one_mem_and_smul_top_le_of_quotient_span_eq_top
    {I : Ideal R} [Module.Finite R M] (s : Set M)
    (hgen : Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' s) = ⊤) :
    ∃ r : R,
      r - 1 ∈ I ∧ r • (⊤ : Submodule R M) ≤ Submodule.span R s ∧
        (Submodule.span R s).localized (Submonoid.powers r) = ⊤ := sorry

/-- If a family generates a finite module modulo an ideal, then its span becomes the whole module
after localizing away from some element congruent to `1` modulo that ideal. -/
@[stacks 00DV "Nakayama localized quotient-span generation projection"]
theorem exists_sub_one_mem_and_localized_eq_top_of_quotient_span_eq_top
    {I : Ideal R} [Module.Finite R M] (s : Set M)
    (hgen : Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' s) = ⊤) :
    ∃ r : R,
      r - 1 ∈ I ∧ (Submodule.span R s).localized (Submonoid.powers r) = ⊤ := sorry

/-- A submodule is the whole module when it generates modulo a finitely generated submodule over
an ideal in the Jacobson radical. -/
@[stacks 00DV "Nakayama generation criterion"]
theorem eq_top_of_sup_eq_top_of_le_jacobson
    (I : Ideal R) (N N' : Submodule R M) (hN' : N'.FG)
    (hNN' : N ⊔ I • N' = ⊤) (hIjac : I ≤ Ring.jacobson R) : N = ⊤ := sorry

/-- A finite family generates a module when its image modulo an ideal in the Jacobson radical
generates the quotient module. -/
@[stacks 00DV "Nakayama finite generation criterion"]
theorem span_eq_top_of_quotient_span_eq_top_of_le_jacobson
    (I : Ideal R) [Module.Finite R M] (s : Finset M)
    (hgen : Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' (s : Set M)) = ⊤)
    (hIjac : I ≤ Ring.jacobson R) : Submodule.span R (s : Set M) = ⊤ := sorry

/-- A submodule is the whole module when it generates modulo a nilpotent ideal. -/
@[stacks 00DV "nilpotent Nakayama generation criterion"]
theorem eq_top_of_sup_eq_top_of_isNilpotent
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (N N' : Submodule R M)
    (hNN' : N ⊔ I • N' = ⊤) (hI : IsNilpotent I) : N = ⊤ := sorry

/-- A family generates a module when its image modulo a nilpotent ideal generates the quotient
module. -/
@[stacks 00DV "nilpotent Nakayama generation by a family"]
theorem span_eq_top_of_quotient_span_eq_top_of_isNilpotent
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (s : Set M)
    (hgen : Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' s) = ⊤)
    (hI : IsNilpotent I) : Submodule.span R s = ⊤ := sorry

end Submodule
