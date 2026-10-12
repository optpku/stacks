/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.Equivalence
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Discrete
public import ReasLib.CategoryTheory.Fibered.HomPresheaf
public import ReasLib.CategoryTheory.Fibered.InSetoids
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Isom
import Mathlib.Tactic.CrossRefAttribute

/-!
# The fibred category represented by an isomorphism presheaf

The isomorphism presheaf of two objects in a fibre has a canonical discrete Grothendieck
construction over the corresponding slice category. This gives an invariant formal model for the
two-fibre product appearing in Stacks Project, Lemma 8.2.5: the redundant intermediate object and
its two comparison isomorphisms are replaced by their composite isomorphism.

The construction is kept at the projection level. It therefore applies to every fibred functor,
without requiring a bundled `FiberedCategoryOver` or a groupoid hypothesis on its total category.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Opposite

namespace Functor

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} [Category.{vS} S]

/-- The canonical isomorphism presheaf of two objects in the same fibre of a fibred functor. -/
noncomputable abbrev isomorphismPresheaf
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) :
    (Over U)ᵒᵖ ⥤ Type vS :=
  (Pseudofunctor.isomSubpresheaf (fiberPseudofunctor p) x y).toFunctor

/-- The universe-raised isomorphism presheaf used by its size-stable Grothendieck construction. -/
noncomputable abbrev isomorphismPresheafULift
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) :
    (Over U)ᵒᵖ ⥤ Type (max vS (max u v)) :=
  isomorphismPresheaf p x y ⋙
    (CategoryTheory.uliftFunctor.{max u v, vS} :
      Type vS ⥤ Type (max vS (max u v)))

/-- The discrete Grothendieck construction of the isomorphism presheaf of two fibre objects.

Its objects over `a : V ⟶ U` are isomorphisms between the reindexings of `x` and `y` along
`a`. This is the skeletal Grothendieck model of the presentation by an intermediate object `z`
and isomorphisms from `z` to those two reindexings. -/
noncomputable def isomorphismGrothendieck
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) :=
  (FiberedCategoryOver.Sets.ofPresheaf (Over U)).obj
    (isomorphismPresheaf p x y)

/-- The size-stable discrete Grothendieck construction of the universe-raised isomorphism
presheaf. Use this owner when the resulting fibre-object presheaf must live in the universe of the
slice category. -/
noncomputable def isomorphismGrothendieckULift
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) :=
  (FiberedCategoryOver.Sets.ofPresheaf (Over U)).obj
    (isomorphismPresheafULift p x y)

/- The non-`Prop` data of both owners are explicit category-of-elements constructions. Deferred
axioms in their generic owners occur only in functor laws and owner-membership proofs. -/

/-- Lemma 8.2.5 (1) (Stacks 04SI): the canonical two-fibre-product model is fibred in setoids.

The owner is in fact a discrete fibration, so this statement deliberately exposes the weaker,
equivalence-invariant conclusion used by the source. -/
theorem isomorphismGrothendieck.inSetoids
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) :
    IsFibered.InSetoids (isomorphismGrothendieck p x y).p := sorry

/-- The size-stable Grothendieck owner is also canonically fibred in setoids. -/
theorem isomorphismGrothendieckULift.inSetoids
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) :
    IsFibered.InSetoids (isomorphismGrothendieckULift p x y).p := sorry

/-- Straightening the size-stable Grothendieck owner recovers the universe-raised isomorphism
presheaf. -/
noncomputable def isomorphismGrothendieckULift.presheafIso
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) :
    (FiberedCategoryOver.Sets.toPresheaf (Over U)).obj
        (isomorphismGrothendieckULift p x y) ≅
      isomorphismPresheafULift p x y :=
  FiberedCategoryOver.Sets.PresheafEquivalence.toObjIso
    (isomorphismPresheafULift p x y)

/-- The isomorphism-class presheaf of the size-stable Grothendieck owner is canonically the
universe-raised isomorphism presheaf. -/
noncomputable def isomorphismGrothendieckULift.isoClassPresheafIso
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) :
    Functor.fiberIsoClassPresheaf (isomorphismGrothendieckULift p x y).p ≅
      isomorphismPresheafULift p x y :=
  Functor.IsDiscreteFibration.fiberClassesIso
      (isomorphismGrothendieckULift p x y).p ≪≫
    isomorphismGrothendieckULift.presheafIso p x y

end Functor

end CategoryTheory
