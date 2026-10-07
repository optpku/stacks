module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import stacks_project.Chap100.Definition_100_4_2_Points

/-!
# Points of a 2-fibre product of algebraic stacks

A 2-fibre product square of algebraic stacks over a scheme `S` induces a comparison from the
points of the apex to the set-theoretic fibre product of points. That comparison is
surjective, though not in general injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Bicategory

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Points

/-- The set-theoretic fibre product of points of algebraic stacks over a common target.

This is the mathlib cospan order `|X| ×_{|Y|} |Z|`; the Stacks source writes the swapped product
`|Z| ×_{|Y|} |X|`. -/
abbrev pullbackObj {S : Scheme.{u}} {X Z Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] [AlgebraicStack Y]
    (f : X ⟶ Y) (g : Z ⟶ Y) : Type (u + 1) :=
  Types.PullbackObj (TypeCat.ofHom (map f)) (TypeCat.ofHom (map g))

section

variable {S : Scheme.{u}} {P X Z Y : GroupoidsOver S}
variable [AlgebraicStack P] [AlgebraicStack X] [AlgebraicStack Z] [AlgebraicStack Y]
variable {fst : P ⟶ X} {snd : P ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}

/-- The readable 2-commutative square with apex `P` associated to a 2-fibre product of algebraic
stacks. -/
def cone (iso : fst ≫ f ≅ snd ≫ g) : PseudoPullbackCone f g :=
  ⟨P, fst, snd, iso⟩

/-- The two legs of a 2-fibre product square of algebraic stacks agree after mapping to points of
the common target. -/
theorem pullbackComparison_condition (iso : fst ≫ f ≅ snd ≫ g) (h : (cone iso).IsBilimit)
    (p : Points P) : map f (map fst p) = map g (map snd p) := sorry

/-- The comparison of points associated to a 2-fibre product square of algebraic stacks. -/
def pullbackComparison (iso : fst ≫ f ≅ snd ≫ g) (h : (cone iso).IsBilimit) :
    Points P → pullbackObj f g :=
  fun p ↦ ⟨(map fst p, map snd p), pullbackComparison_condition iso h p⟩

/-- The first component of the points comparison is the map on points induced by `fst`. -/
theorem pullbackComparison_fst (iso : fst ≫ f ≅ snd ≫ g) (h : (cone iso).IsBilimit)
    (p : Points P) : (pullbackComparison iso h p).1.1 = map fst p := sorry

/-- The second component of the points comparison is the map on points induced by `snd`. -/
theorem pullbackComparison_snd (iso : fst ≫ f ≅ snd ≫ g) (h : (cone iso).IsBilimit)
    (p : Points P) : (pullbackComparison iso h p).1.2 = map snd p := sorry

/-- The points comparison sends a point of the apex to the compatible pair of its images. -/
theorem pullbackComparison_apply (iso : fst ≫ f ≅ snd ≫ g) (h : (cone iso).IsBilimit)
    (p : Points P) :
    pullbackComparison iso h p =
      ⟨(map fst p, map snd p), pullbackComparison_condition iso h p⟩ := sorry

/-- The comparison of points of a 2-fibre product square of algebraic stacks is surjective. -/
theorem pullbackComparison_surjective (iso : fst ≫ f ≅ snd ≫ g) (h : (cone iso).IsBilimit) :
    Function.Surjective (pullbackComparison iso h) := sorry

/-- A compatible pair of points of `X` and `Z` over `Y` lifts to a point of a 2-fibre product
apex. -/
theorem exists_of_map_eq (iso : fst ≫ f ≅ snd ≫ g) (h : (cone iso).IsBilimit)
    (x : Points X) (z : Points Z) (hxz : map f x = map g z) :
    ∃ p : Points P, map fst p = x ∧ map snd p = z := sorry

end

end AlgebraicGeometry.AlgebraicStack.Points
