/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import ReasLib.Topology.Sheaf.Subset.General
public import ReasLib.Topology.Sheaf.Support
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheaves on closed subsets: stalk vanishing and essential image

For a closed subset `Z ⊆ X`, the pushforward of a sheaf on `Z` has trivial stalks at points
not in `Z`. This characterizes the essential image of the closed-subset pushforward functor.

## Main declarations

- `TopCat.Sheaf.ClosedSubset.stalk_isTerminal_of_not_mem`: stalk vanishes outside `Z`
- `TopCat.Sheaf.ClosedSubset.essImage_iff`: essential image characterization
- `TopCat.Sheaf.ClosedSubset.AddCommGrp.stalk_isZero_of_not_mem`: additive version
- `TopCat.Sheaf.ClosedSubset.not_preservesBinaryCoproducts`: a proper closed inclusion gives a
  pushforward that is not cocontinuous
- `TopCat.Sheaf.ClosedSubset.not_rightExact`: that pushforward is not right exact
- `TopCat.Sheaf.ClosedSubset.not_isLeftAdjoint`: that pushforward has no right adjoint
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open scoped TopCat

noncomputable section

universe v w

namespace TopCat.Sheaf.ClosedSubset

variable {X : TopCat.{v}}

section TypeValued

/-- For a closed subset `Z`, the stalk of the pushforward of a `Type`-valued sheaf at a point
not in `Z` is terminal. -/
@[stacks 00AE "pushforward stalk outside closed subset is terminal"]
theorem type_stalk_isTerminal_of_not_mem (Z : Set X) (hZ : IsClosed Z)
    (G : TopCat.Sheaf (Type v) (TopCat.subsetSpace Z))
    (x : X) (hx : x ∉ Z) :
    Nonempty (IsTerminal (((TopCat.Sheaf.pushforward (Type v)
      (TopCat.subsetInclusion Z)).obj G).presheaf.stalk x)) := sorry

end TypeValued

section General

variable {C : Type w} [Category.{v} C]
variable {FC : C → C → Type v} {CC : C → Type v}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory.{v} C FC]
variable [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]

/-- For a closed subset `Z`, the stalk of the pushforward at a point not in `Z` is terminal. -/
@[stacks 00AE "algebraic pushforward stalk outside closed subset is terminal"]
theorem stalk_isTerminal_of_not_mem (Z : Set X) (hZ : IsClosed Z)
    (G : TopCat.Sheaf C (TopCat.subsetSpace Z))
    (x : X) (hx : x ∉ Z) :
    Nonempty (IsTerminal (((TopCat.Sheaf.pushforward C
      (TopCat.subsetInclusion Z)).obj G).presheaf.stalk x)) := sorry

section EssentialImage

/-- A sheaf on `X` is in the essential image of the closed-subset pushforward iff its stalks
outside `Z` are terminal (filtered-stalk version). -/
theorem essImage_iff_filteredStalk_isTerminal_of_not_mem (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf C X) :
    (TopCat.Sheaf.pushforward C (TopCat.subsetInclusion Z)).essImage F ↔
      ∀ x : X, x ∉ Z →
        Nonempty (IsTerminal (TopCat.Presheaf.filteredStalk (X := X) x F.presheaf)) := sorry

/-- Essential image characterized by ordinary stalks. -/
theorem essImage_iff_stalk_isTerminal_of_not_mem (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf C X) :
    (TopCat.Sheaf.pushforward C (TopCat.subsetInclusion Z)).essImage F ↔
      ∀ x : X, x ∉ Z → Nonempty (IsTerminal (F.presheaf.stalk x)) := sorry

end EssentialImage

end General

section TypeEssentialImage

/-- Type-valued essential image characterization. -/
theorem type_essImage_iff_stalk_isTerminal_of_not_mem
    (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf (Type v) X) :
    (TopCat.Sheaf.pushforward (Type v) (TopCat.subsetInclusion Z)).essImage F ↔
      ∀ x : X, x ∉ Z → Nonempty (IsTerminal (F.presheaf.stalk x)) := sorry

end TypeEssentialImage

namespace AddCommGrp

variable {Z : Set X}

/-- For `AddCommGrp`-valued sheaves, the stalk at a point not in `Z` is zero. -/
@[stacks 00AE "abelian pushforward stalk outside closed subset is zero"]
theorem stalk_isZero_of_not_mem (hZ : IsClosed Z)
    (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.subsetSpace Z))
    (x : X) (hx : x ∉ Z) :
    IsZero (((TopCat.Sheaf.pushforward AddCommGrpCat.{v}
      (TopCat.subsetInclusion Z)).obj G).presheaf.stalk x) := sorry

/-- `AddCommGrp`-valued essential image characterized by zero stalks. -/
theorem essImage_iff_stalk_isZero_of_not_mem (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{v}
      (TopCat.subsetInclusion Z)).essImage F ↔
      ∀ x : X, x ∉ Z → IsZero (F.presheaf.stalk x) := sorry

/-- Pushforward from a closed subset is exact on abelian sheaves. -/
@[stacks 01AX "(1)"]
theorem pushforwardExact (hZ : IsClosed Z) :
    exactFunctor ((TopCat.of Z).Sheaf AddCommGrpCat.{v})
      (X.Sheaf AddCommGrpCat.{v})
      (TopCat.Sheaf.pushforward AddCommGrpCat.{v} (TopCat.subsetInclusion Z)) := sorry

/-- An abelian sheaf is in the essential image of pushforward from a closed subset exactly when
its support is contained in that subset. -/
@[stacks 01AX "(3)"]
theorem essImage_iff_support_subset
    (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{v}) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{v}
      (TopCat.subsetInclusion Z)).essImage F ↔
      abelianSheafSupport F ⊆ Z := sorry

end AddCommGrp

section NonExactness

/-- If the complement of a closed subset contains `x`, its `Type`-valued pushforward does not
preserve binary coproducts. The point hypothesis is essential: the inclusion of all of `X` is the
identity functor. -/
theorem not_preservesBinaryCoproducts (Z : Set X) (hZ : IsClosed Z) (x : X) (hx : x ∉ Z) :
    ¬ PreservesColimitsOfShape (Discrete WalkingPair)
      (TopCat.Sheaf.pushforward (Type v) (TopCat.subsetInclusion Z)) := sorry

/-- Under the same properness witness, the closed-subset pushforward is not right exact. -/
theorem not_rightExact (Z : Set X) (hZ : IsClosed Z) (x : X) (hx : x ∉ Z) :
    ¬ rightExactFunctor
      ((TopCat.subsetSpace Z).Sheaf (Type v)) (X.Sheaf (Type v))
      (TopCat.Sheaf.pushforward (Type v) (TopCat.subsetInclusion Z)) := sorry

/-- Under the same properness witness, the closed-subset pushforward has no right adjoint. -/
theorem not_isLeftAdjoint (Z : Set X) (hZ : IsClosed Z) (x : X) (hx : x ∉ Z) :
    ¬ (TopCat.Sheaf.pushforward (Type v)
      (TopCat.subsetInclusion Z)).IsLeftAdjoint := sorry

end NonExactness

end TopCat.Sheaf.ClosedSubset

end

end
