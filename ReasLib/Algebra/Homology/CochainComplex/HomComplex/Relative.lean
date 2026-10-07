module

public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.FiniteWindow
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.FinitePresentation
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.FiniteProjective
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative finiteness and flatness of Hom complexes

For a bounded-above finite-projective source and a bounded-below target, each degree of the
enriched Hom complex is a finite product over a canonical support window.  This file records the
relative-flat and finite-presentation consequences independently of any derived-category model.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace CochainComplex.HomComplex

variable {A : Type v} [CommRing A]

/-- Relative termwise flatness of a target passes to its Hom complex from a bounded-above
termwise finite-projective source. -/
@[stacks 0E1U "relative termwise flatness of a Hom complex"]
theorem isTermwiseFlatAlong
    {R : Type u} [CommRing R] (σ : R →+* A) (P F : CochainComplex (ModuleCat A) ℤ)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F)
    (hFflat : F.IsTermwiseFlatAlong σ) :
    (moduleComplex A P F).IsTermwiseFlatAlong σ := sorry
/- Proof strategy: restrict the Hom complex degreewise to its finite support window; each factor
is a finite-projective dual of a restricted flat target, and finite products preserve flatness. -/

/-- The algebra-specialized form of relative termwise flatness for a fixed Hom complex. -/
@[stacks 0E1U "termwise flatness over a base of a Hom complex"]
theorem isTermwiseFlatOver
    {R : Type u} [CommRing R] [Algebra R A]
    (P F : CochainComplex (ModuleCat A) ℤ)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F)
    (hFflat : F.IsTermwiseFlatOver R) :
    (moduleComplex A P F).IsTermwiseFlatOver R := sorry
/- Proof strategy: specialize `isTermwiseFlatAlong` to `algebraMap R A` and unfold the two
algebra-specialized restriction predicates. -/

/-- Termwise finite presentation of a target passes to its Hom complex from a bounded-above
termwise finite-projective source. -/
@[stacks 0E1U "termwise finite presentation of a Hom complex"]
theorem isTermwiseFinitePresentation
    (P F : CochainComplex (ModuleCat A) ℤ)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F)
    (hFfp : F.IsTermwiseFinitePresentation) :
    (moduleComplex A P F).IsTermwiseFinitePresentation := sorry
/- Proof strategy: use the finite support window and the finite-projective component API to
express each Hom degree as a finite presentation built from the target components. -/

end CochainComplex.HomComplex
