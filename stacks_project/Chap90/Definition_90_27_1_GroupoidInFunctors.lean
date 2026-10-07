module

public import Mathlib.CategoryTheory.Elements
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_21_1_Groupoid
public import stacks_project.Chap90.Definition_90_23_1

/-!
# Prorepresentable groupoids in functors

A groupoid in functors on `ArtinianLocalAlgCat Λ k` is prorepresentable when both
its object functor and its arrow functor are prorepresentable.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v w

namespace CategoryTheory.GroupoidInFunctors

section SourceTarget

variable {C : Type u} [Category.{v} C]

/-- The based functor over `C` induced by the source map of a groupoid in functors. -/
def sourceBasedFunctor (G : GroupoidInFunctors C) :
    BasedCategory.ofFunctor (CategoryOfElements.π G.R) ⥤ᵇ
      BasedCategory.ofFunctor (CategoryOfElements.π G.U) :=
  BasedFunctor.ofFunctor (CategoryOfElements.map G.s) (CategoryOfElements.map_π G.s)

/-- The underlying functor of `sourceBasedFunctor` is the category-of-elements map of `s`. -/
theorem sourceBasedFunctor_toFunctor (G : GroupoidInFunctors C) :
    (sourceBasedFunctor G).toFunctor = CategoryOfElements.map G.s :=
  rfl

/-- The based functor over `C` induced by the target map of a groupoid in functors. -/
def targetBasedFunctor (G : GroupoidInFunctors C) :
    BasedCategory.ofFunctor (CategoryOfElements.π G.R) ⥤ᵇ
      BasedCategory.ofFunctor (CategoryOfElements.π G.U) :=
  BasedFunctor.ofFunctor (CategoryOfElements.map G.t) (CategoryOfElements.map_π G.t)

/-- The underlying functor of `targetBasedFunctor` is the category-of-elements map of `t`. -/
theorem targetBasedFunctor_toFunctor (G : GroupoidInFunctors C) :
    (targetBasedFunctor G).toFunctor = CategoryOfElements.map G.t :=
  rfl

end SourceTarget

section Prorepresentable

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- A groupoid in functors on `ArtinianLocalAlgCat Λ k` is prorepresentable when both
`U` and `R` are prorepresentable functors. -/
class IsProrepresentable
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) : Prop where
  /-- The object functor is prorepresentable. -/
  isProrepresentable_U : Functor.IsProrepresentable G.U
  /-- The arrow functor is prorepresentable. -/
  isProrepresentable_R : Functor.IsProrepresentable G.R

/-- The object functor of a prorepresentable groupoid in functors is prorepresentable. -/
instance instIsProrepresentable_U
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [h : IsProrepresentable G] : Functor.IsProrepresentable G.U :=
  h.isProrepresentable_U

/-- The arrow functor of a prorepresentable groupoid in functors is prorepresentable. -/
instance instIsProrepresentable_R
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [h : IsProrepresentable G] : Functor.IsProrepresentable G.R :=
  h.isProrepresentable_R

/-- Prorepresentability of a groupoid in functors is prorepresentability of both
structure functors. -/
theorem isProrepresentable_iff
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :
    IsProrepresentable G ↔
      Functor.IsProrepresentable G.U ∧ Functor.IsProrepresentable G.R :=
  sorry

/-- A prorepresentable groupoid in functors has prorepresentable object and arrow
functors. -/
theorem isProrepresentable_spec
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsProrepresentable G] :
    Functor.IsProrepresentable G.U ∧ Functor.IsProrepresentable G.R :=
  sorry

/-- The discrete groupoid on a restricted coyoneda functor is prorepresentable. -/
instance instIsProrepresentableDiscrete (R : CompleteLocalAlgCat Λ k) :
    IsProrepresentable (discrete (CompleteLocalAlgCat.restrictedCoyoneda R)) where
  isProrepresentable_U := Functor.instIsProrepresentableRestrictedCoyoneda R
  isProrepresentable_R := Functor.instIsProrepresentableRestrictedCoyoneda R

/-- The discrete groupoid on a restricted coyoneda functor has smooth source and
target maps. -/
instance instIsSmoothDiscrete (R : CompleteLocalAlgCat Λ k) :
    IsSmooth (discrete (CompleteLocalAlgCat.restrictedCoyoneda R)).s
      (discrete (CompleteLocalAlgCat.restrictedCoyoneda R)).t :=
  instIsSmoothId

end Prorepresentable

end CategoryTheory.GroupoidInFunctors
