module

public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
public import ReasLib.Algebra.Homology.CochainComplex.Module
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.CategoryTheory.Preadditive.CompactObject
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfectness of Finite Graded Projective Complexes

This leaf gives the derived-category consequences of the finite graded
projective predicate from `CochainComplex.FiniteProjective`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory

universe u

namespace CochainComplex

variable {R : Type u} [Ring R]

namespace IsFiniteGradedProjective

/-- A finite graded projective complex represents a perfect object of the derived category. -/
theorem isPerfect {P : ModuleCat.DGMod R} (hP : P.IsFiniteGradedProjective) :
    ((DerivedCategory.Q : ModuleCat.DGMod R ⥤ DerivedCategory (ModuleCat R)).obj P).IsPerfect := sorry

/-- A finite graded projective cochain complex represents a compact object of the derived
category of modules over its ground ring. -/
theorem isCompactObject {P : ModuleCat.DGMod R} (hP : P.IsFiniteGradedProjective) :
    IsCompactObject
      ((DerivedCategory.Q : ModuleCat.DGMod R ⥤ DerivedCategory (ModuleCat R)).obj P) := sorry

end IsFiniteGradedProjective

end CochainComplex
