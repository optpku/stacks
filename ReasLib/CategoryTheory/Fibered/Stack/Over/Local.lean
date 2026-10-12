/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Over.Hom
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Local
public import ReasLib.CategoryTheory.Fibered.Stack.LocalEquivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local equivalence criteria for morphisms of stacks

This module exposes the standard over-base equivalence and local essential-surjectivity
predicates directly on a morphism of bundled stacks. The canonical local predicate belongs to
`CartesianBasedFunctor`; the intermediate `FiberedCategoryOver.Hom` and this stack layer are
fixed-universe specializations.

## Main declarations

* `StackOver.Hom.LocallyEssentiallySurjective` -- local essential surjectivity on
  fiber objects.
* `StackOver.Hom.IsEquivalence.iff_locallyEssentiallySurjective` -- the fully faithful
  criterion.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

namespace StackOver.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackOver.{u, v, w, vS} J}

/-- Every target fiber object is locally in the essential image of a morphism of bundled
stacks.  The site is inferred from the source and target stack owners. -/
@[stacks 046N "local essential surjectivity for a stack morphism"]
abbrev LocallyEssentiallySurjective (F : X ⟶ Y) : Prop :=
  FiberedCategoryOver.Hom.LocallyEssentiallySurjective J (toMor F)

/-- Lemma 8.4.8 (tag 046N), fixed-universe bundled specialization: for a fully faithful
morphism of stacks over a site, being an equivalence over the base is equivalent to local
essential surjectivity on fiber objects. -/
@[stacks 046N "bundled fixed-universe form"]
theorem IsEquivalence.iff_locallyEssentiallySurjective
    (F : X ⟶ Y) (h_fullyFaithful : Nonempty (toBasedFunctor F).FullyFaithful) :
    IsEquivalence F ↔ LocallyEssentiallySurjective F := sorry

end StackOver.Hom

end CategoryTheory
