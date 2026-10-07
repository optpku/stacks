module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.SetTheory.Cardinal.Basic
public import stacks_project.Chap03.Lemma_3_9_4_Size
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Bounded finite-type field fibres

Axiom [-1] of Section 98.14: a category fibred in groupoids over `(Sch/S)_fppf`
has a uniform Stacks-size bound on both isomorphism classes of objects and
arrows of its fibres over finite-type fields.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Cardinal

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Axiom [-1]: there is a scheme `T` over `S` whose Stacks size bounds both
the cardinal of isomorphism classes of objects and the cardinal of arrows of
every fibre `X_{Spec(k)}`, as `k` runs over finite-type fields over `S`. -/
class HasBoundedFiniteTypeFibers {S : Scheme.{u}} (X : GroupoidsOver S) : Prop where
  /-- Some object of `(Sch/S)_fppf` bounds all finite-type field fibres. -/
  exists_bound :
    ∃ T : Over S,
      ∀ {k : Type u} [Field k] (kToS : Spec (CommRingCat.of k) ⟶ S)
        [LocallyOfFiniteType kToS],
        #(Quotient (isIsomorphicSetoid (X.p.Fiber (Over.mk kToS)))) ≤
            Cardinal.lift.{u + 1} T.left.size ∧
          #(Arrow (X.p.Fiber (Over.mk kToS))) ≤
            Cardinal.lift.{u + 1} T.left.size

namespace HasBoundedFiniteTypeFibers

/-- The canonical slice fibration of a scheme over `S` satisfies axiom [-1]. -/
instance slice {S : Scheme.{u}} (U : Over S) :
    HasBoundedFiniteTypeFibers (GroupoidsOver.slice U) :=
  sorry

/-- Axiom [-1] supplies a scheme over `S` bounding both iso-class and arrow
cardinals of every finite-type field fibre. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S)
    [HasBoundedFiniteTypeFibers X] :
    ∃ T : Over S,
      ∀ {k : Type u} [Field k] (kToS : Spec (CommRingCat.of k) ⟶ S)
        [LocallyOfFiniteType kToS],
        #(Quotient (isIsomorphicSetoid (X.p.Fiber (Over.mk kToS)))) ≤
            Cardinal.lift.{u + 1} T.left.size ∧
          #(Arrow (X.p.Fiber (Over.mk kToS))) ≤
            Cardinal.lift.{u + 1} T.left.size :=
  sorry

/-- Axiom [-1] is equivalent to the existence of one scheme over `S` bounding
both iso-class and arrow cardinals of every finite-type field fibre. -/
theorem iff {S : Scheme.{u}} (X : GroupoidsOver S) :
    HasBoundedFiniteTypeFibers X ↔
      ∃ T : Over S,
        ∀ {k : Type u} [Field k] (kToS : Spec (CommRingCat.of k) ⟶ S)
          [LocallyOfFiniteType kToS],
          #(Quotient (isIsomorphicSetoid (X.p.Fiber (Over.mk kToS)))) ≤
              Cardinal.lift.{u + 1} T.left.size ∧
            #(Arrow (X.p.Fiber (Over.mk kToS))) ≤
              Cardinal.lift.{u + 1} T.left.size :=
  sorry

end HasBoundedFiniteTypeFibers

end AlgebraicGeometry.GroupoidsOver
