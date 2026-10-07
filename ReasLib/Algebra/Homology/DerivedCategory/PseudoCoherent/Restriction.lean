module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Homology
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of scalars and pseudo-coherence

This leaf owns the change-of-rings surface for absolute pseudo-coherence.  The restriction functor
and its homology comparison are explicit data; the two preservation/reflection equivalences are
statement-level API whose proofs can be completed independently of the chapter presentation.

@stack 064Z
@stack 065G
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

variable {A B : Type u} [Ring A] [Ring B]

namespace ModuleCat.RestrictScalars

/-- Restriction of scalars commutes with derived homology, with the comparison object made
explicit. -/
@[stacks 064Z "restriction of scalars and homology"]
noncomputable def homologyIso
    (f : A →+* B) (L : DerivedCategory (ModuleCat B)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat A) i).obj
        (((ModuleCat.restrictScalars f).mapDerivedCategory).obj L) ≅
    (ModuleCat.restrictScalars f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat B) i).obj L) :=
  (Functor.MapDerivedCategory.homologyIso
    (ModuleCat.RestrictScalars.exact f).obj L i)

/-- Restriction of scalars reflects zero module objects because it does not change the underlying
additive group. -/
@[stacks 064Z "restriction reflects zero objects"]
theorem isZero_of_obj
    (f : A →+* B) (M : ModuleCat B)
    (hM : IsZero ((ModuleCat.restrictScalars f).obj M)) :
    IsZero M :=
  (ModuleCat.RestrictScalars.isZero_obj_iff f M).1 hM

end ModuleCat.RestrictScalars

namespace DerivedCategory.IsMPseudoCoherent

/-- Lemma 15.65.11 (1): under pseudo-coherence of the restricted regular module, `m`-pseudo-
coherence is equivalent before and after restriction of scalars. -/
@[stacks 064Z "(1), restriction-of-scalars equivalence"]
theorem iff_restrictScalars
    (f : A →+* B) (K : DerivedCategory (ModuleCat B)) (m : ℤ)
    (hB : ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)).IsPseudoCoherent) :
    K.IsMPseudoCoherent m ↔
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K).IsMPseudoCoherent m := sorry

/-- Lemma 15.82.2 (065G): evaluation at zero along `R[X] → R` preserves and reflects
`m`-pseudo-coherence of derived complexes. -/
@[stacks 065G "polynomial evaluation at zero and m-pseudo-coherence"]
theorem iff_restrictScalars_polynomialEvalZero
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat R)) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      ((ModuleCat.restrictScalars (Polynomial.evalRingHom (0 : R))).mapDerivedCategory.obj K).IsMPseudoCoherent m := sorry

end DerivedCategory.IsMPseudoCoherent

namespace DerivedCategory.IsPseudoCoherent

/-- Lemma 15.65.11 (2): under pseudo-coherence of the restricted regular module, pseudo-coherence
is equivalent before and after restriction of scalars. -/
@[stacks 064Z "(2), restriction-of-scalars equivalence"]
theorem iff_restrictScalars
    (f : A →+* B) (K : DerivedCategory (ModuleCat B))
    (hB : ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)).IsPseudoCoherent) :
    K.IsPseudoCoherent ↔
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K).IsPseudoCoherent := sorry

end DerivedCategory.IsPseudoCoherent

end CategoryTheory

end
