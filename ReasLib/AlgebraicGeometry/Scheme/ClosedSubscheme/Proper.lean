/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Pullback

/-!
# Proper closed subsets over a base scheme

This leaf defines properness over a base for a closed subset through its
canonical reduced induced closed subscheme. The definition is a transparent
view of Mathlib's `IsProper` predicate; local finite type is needed only by the
comparison theorem for arbitrary closed-subscheme structures.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace ClosedSubset

/-- A closed subset `Z ⊆ X` is proper over `S` when its reduced induced closed subscheme is
proper over `S`. -/
@[stacks 0CYM]
abbrev IsProperOver
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : TopologicalSpace.Closeds X) : Prop :=
  IsProper ((Scheme.ClosedSubschemeStructure.reduced Z).ι ≫ f)

/-- Properness over a base is inherited by closed subsets. -/
theorem IsProperOver.mono
    {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    {Y Z : TopologicalSpace.Closeds X} (hYZ : Y ≤ Z) [hZ : IsProperOver f Z] :
    IsProperOver f Y := by
  change IsProper ((Scheme.IdealSheafData.vanishingIdeal Y).subschemeι ≫ f)
  rw [← Scheme.IdealSheafData.inclusion_subschemeι
    (Scheme.IdealSheafData.vanishingIdeal_antimono hYZ), Category.assoc]
  exact MorphismProperty.comp_mem (@IsProper)
    (Scheme.IdealSheafData.inclusion
      (Scheme.IdealSheafData.vanishingIdeal_antimono hYZ))
    ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f)
    inferInstance hZ

/-- Properness of a closed subset over a base is equivalent to properness for some, equivalently
every, closed-subscheme structure with the same underlying closed subset. -/
@[stacks 0CYL]
theorem isProperOver_tfae
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z : TopologicalSpace.Closeds X) :
    List.TFAE [
      IsProperOver f Z,
      ∃ T : Scheme.ClosedSubschemeStructure Z, IsProper (T.ι ≫ f),
      ∀ T : Scheme.ClosedSubschemeStructure Z, IsProper (T.ι ≫ f)
    ] := sorry

/-- Properness of a closed subset over a base is preserved by inverse image in a cartesian
square. -/
theorem IsProperOver.preimage
    {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (sq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (Z : TopologicalSpace.Closeds X)
    [IsProperOver f Z] :
    IsProperOver f' (Z.preimage g'.continuous) := sorry

end ClosedSubset

end AlgebraicGeometry
