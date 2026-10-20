module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.SetTheory.Cardinal.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Size
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic

/-!
# Bounded finite-type field fibres

A category fibred in groupoids over `(Sch/S)_fppf` has bounded finite-type
field fibres when one scheme over `S` uniformly bounds the cardinalities of
both isomorphism classes of objects and arrows in these fibres.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Cardinal

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- There is a scheme `T` over `S` whose size bounds both
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

/-- The canonical slice fibration of a scheme over `S` has uniformly bounded
finite-type field fibres. -/
instance slice {S : Scheme.{u}} (U : Over S) :
    HasBoundedFiniteTypeFibers (GroupoidsOver.slice U) :=
  sorry

/-- Bounded finite-type field fibres admit one scheme over `S` bounding both
isomorphism-class and arrow cardinals of every such fibre. -/
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

/-- Boundedness of finite-type field fibres is equivalent to the existence of
one scheme over `S` bounding both isomorphism-class and arrow cardinals of
every such fibre. -/
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
