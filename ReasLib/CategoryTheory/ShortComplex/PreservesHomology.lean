/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Functoriality of Short-Complex Homology Descents

This module complements mathlib's preservation isomorphisms with a computation rule for maps
defined by descent from cycles.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {F : C ⥤ C} [F.PreservesZeroMorphisms]
variable {S : ShortComplex C} [HasHomology S] [HasHomology (S.map F)]
variable [F.PreservesLeftHomologyOf S]

/-- Mapping a homology descent through `mapHomologyIso` agrees with descending the mapped cycles
representative. -/
theorem mapHomologyIso_hom_comp_descHomology {A : C}
    (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0)
    (hk_map : (S.map F).toCycles ≫ ((S.mapCyclesIso F).hom ≫ F.map k) = 0) :
    (S.mapHomologyIso F).hom ≫ F.map (S.descHomology k hk) =
      (S.map F).descHomology ((S.mapCyclesIso F).hom ≫ F.map k) hk_map := sorry

end ShortComplex
end CategoryTheory
