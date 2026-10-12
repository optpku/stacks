/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.Functor.PresheafFiber

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (u : C ⥤ Type (max u v))
variable [InitiallySmall.{max u v} u.Elements] [IsCofiltered u.Elements]

/- Lemma 7.33.1 (Stacks, Section 7.33, tag `05UZ`): if the category of
neighbourhoods of the set-valued functor `u : C ⥤ Type (max u v)` is
cofiltered, then the stalk functor
`sheafToPresheaf J (Type (max u v)) ⋙ u.presheafFiber` is left exact. The
canonical finite-limit-preservation instance is the reusable API; this chapter
file only recalls it. -/
@[stacks 0F4E] #check (inferInstance : PreservesFiniteLimits
  (sheafToPresheaf J (Type (max u v)) ⋙ u.presheafFiber))

end CategoryTheory
