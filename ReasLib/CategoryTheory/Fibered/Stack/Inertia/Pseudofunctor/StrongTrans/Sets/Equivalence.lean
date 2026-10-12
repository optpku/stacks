/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.StrongTrans.Sets

/-!
# The pseudofunctor equivalence induced by set-stack inertia

This leaf packages the objectwise inertia equivalences on stacks in sets as a pseudofunctor
equivalence. Downstream code can transport along inertia without rebuilding inverse
transformations or coherence data.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace StackOver.Sets.Inertia

variable (J : GrothendieckTopology C)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The canonical objectwise inertia equivalences, bundled as pointwise-equivalence data on
set-stack inertia forgetting. -/
@[stacks 04Z3 "pointwise equivalence for set-stack inertia"]
def forget.pointwiseEquivalence :
    Pseudofunctor.StrongTrans.PointwiseEquivalence (forget.strongTrans J) :=
  Pseudofunctor.StrongTrans.PointwiseEquivalence.ofComponents
    (fun X ↦ StackOver.Sets.inertia.forget.equivalence X) (fun _ ↦ Iso.refl _)

/-- Evaluating the pointwise-equivalence data gives the canonical inertia equivalence. -/
@[simp]
theorem forget.pointwiseEquivalence.app
    (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    (forget.pointwiseEquivalence J).app X =
      StackOver.Sets.inertia.forget.equivalence X := sorry

/-- Set-stack inertia is equivalent to the identity pseudofunctor in every inertia-stable
universe. -/
@[stacks 04Z3 "set-stack inertia pseudofunctor equivalence"]
def forget.pseudofunctorEquivalence :
    ((pseudofunctor J) :
        Pseudofunctor
          (StackOver.Sets.{u, v, max w vS, vS} J)
          (StackOver.Sets.{u, v, max w vS, vS} J)) ≌
      Pseudofunctor.id
        (StackOver.Sets.{u, v, max w vS, vS} J) :=
  (forget.pointwiseEquivalence J).toEquivalence

/-- The forward transformation of the pseudofunctor equivalence is inertia forgetting. -/
@[simp]
theorem forget.pseudofunctorEquivalence.hom :
    (forget.pseudofunctorEquivalence.{u, v, w, vS} J).hom =
      forget.strongTrans.{u, v, w, vS} J := sorry

/-- The forward component of the pseudofunctor equivalence is inertia forgetting. -/
@[simp]
theorem forget.pseudofunctorEquivalence.hom.app
    (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    (forget.pseudofunctorEquivalence J).hom.app X =
      StackOver.Sets.inertia.forget X := sorry

/-- The inverse component of the pseudofunctor equivalence is the identity section. -/
@[simp]
theorem forget.pseudofunctorEquivalence.inv.app
    (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    (forget.pseudofunctorEquivalence J).inv.app X =
      StackOver.Sets.inertia.identitySection X := sorry

/-- Evaluating the pseudofunctor equivalence gives the canonical objectwise inertia
equivalence. -/
@[simp]
theorem forget.pseudofunctorEquivalence.app
    (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    (forget.pseudofunctorEquivalence J).app X =
      StackOver.Sets.inertia.forget.equivalence X := sorry

/-- The identity section is the inverse transformation in the canonical inertia
pseudofunctor equivalence. -/
theorem identitySection.strongTrans.eq_inv :
    identitySection.strongTrans.{u, v, w, vS} J =
      (forget.pseudofunctorEquivalence.{u, v, w, vS} J).inv := sorry

end StackOver.Sets.Inertia

end CategoryTheory
