module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Minus
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Model
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Triangulated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded models for pseudo-coherent complexes

This leaf owns the model-level form of Stacks `064U`.  The model carrier is the neutral
`CochainComplex.Minus.TermsIn`; no Chapter 15 alias is needed.  The two term properties below are
kept as explicit predicates so that later developments can replace finite projectives by another
termwise class without rebuilding the pseudo-coherence layer.

@stack 064U
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.CochainComplex

variable {R : Type u} [Ring R]

/-- Finite free `R`-modules, as an object property used by bounded models. -/
@[stacks 064U "finite free term property for pseudo-coherent models"]
abbrev finiteFreeTerms : ObjectProperty (ModuleCat R) :=
  fun M ↦ Module.Free R M ∧ Module.Finite R M

/-- Finite projective `R`-modules, as an object property used by bounded models. -/
@[stacks 064U "finite projective term property for pseudo-coherent models"]
abbrev finiteProjectiveTerms : ObjectProperty (ModuleCat R) :=
  fun M ↦ Module.Finite R M ∧ Projective M

namespace IsPseudoCoherent

/-- Lemma 15.65.5 (1)--(3): pseudo-coherence, all `m`-bounds, and a bounded-above
finite-projective model are equivalent. -/
@[stacks 064U "pseudo-coherence TFAE"]
theorem tfae (K : CochainComplex (ModuleCat R) ℤ) :
    [K.IsPseudoCoherent,
      ∀ m : ℤ, K.IsMPseudoCoherent m,
      ∃ P : CochainComplex.Minus.TermsIn (finiteProjectiveTerms (R := R)),
        ∃ α : (P : CochainComplex (ModuleCat R) ℤ) ⟶ K, QuasiIso α].TFAE := sorry

/-- Lemma 15.65.5: a pseudo-coherent complex with no homology above `b` has a bounded-above
finite-free model with the same upper bound. -/
@[stacks 064U "bounded-above finite-free model with prescribed bound"]
theorem exists_boundedAbove_finiteFree
    {K : CochainComplex (ModuleCat R) ℤ} {b : ℤ}
    (hK : K.IsPseudoCoherent)
    (hvanish : ∀ i : ℤ, b < i → IsZero (K.homology i)) :
    ∃ F : CochainComplex.Minus.TermsIn (finiteFreeTerms (R := R)),
      (F : CochainComplex (ModuleCat R) ℤ).IsStrictlyLE b ∧
        ∃ α : (F : CochainComplex (ModuleCat R) ℤ) ⟶ K, QuasiIso α := sorry

end IsPseudoCoherent

end CategoryTheory.CochainComplex
