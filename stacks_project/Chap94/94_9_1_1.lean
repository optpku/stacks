module

public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.Setoids.AssociatedSets.Basic
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import stacks_project.Chap94.Definition_94_12_1_Representable
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory CategoryTheory.TwoFibreProduct

universe u

section
variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
variable {U : Over S} (y : GroupoidsOver.slice U ⟶ Y)
variable (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U)

/- 94.9.1.1 (1): the right square of the displayed diagram is the 2-commutative
2-fibre product of `y : GroupoidsOver.slice U ⟶ Y` with `f : X ⟶ Y` in
`GroupoidsOver S`. The cone is `TwoFibreProduct.cone y f`, with apex
`TwoFibreProduct.apex y f`, projections `pr0 = TwoFibreProduct.fst` and
`pr1 = TwoFibreProduct.snd`, and 2-commutativity witnessed by
`TwoFibreProduct.comparisonIso`. The square is a 2-fibre product by
`TwoFibreProduct.cone.isBilimit`. -/
@[stacks 0402]
#check (TwoFibreProduct.cone.{u + 1, u, u + 1, u} y f)

#check (TwoFibreProduct.cone.isBilimit.{u + 1, u, u + 1, u} y f)
#check (TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f)
#check (TwoFibreProduct.snd.{u + 1, u, u + 1, u} y f)
#check (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} y f)

/- 94.9.1.1 (2): after choosing an algebraic space `Fy` over `U` representing the
2-fibre product, view `Fy` as an algebraic space over `S` with structure morphism
`fy : Fy ⟶ ofOver U`. The leftward squiggly arrows are the associated sheaf of
isomorphism classes of a category fibred in setoids, given by
`Functor.fiberIsoClassPresheaf` and `FiberedCategoryOver.Setoids.associatedSets`,
and compared with the discrete groupoid fibrations of algebraic spaces through
`AlgebraicSpace.toGroupoids` and `AlgebraicSpace.ofOverSliceEquiv`. -/
@[stacks 0402]
#check (RepresentsBaseChange f y Fy fy)

#check ofOverSliceEquiv
#check toGroupoids
#check RepresentsBaseChange.apex_equivalence
#check RepresentsBaseChange.projection_triangle
#check Functor.fiberIsoClassPresheaf
#check FiberedCategoryOver.Setoids.associatedSets
#check FiberedCategoryOver.Groupoids.baseChange
end

namespace AlgebraicGeometry

/-- The associated sheaf of isomorphism classes of a represented slice 2-fibre
product is naturally isomorphic, after universe lift, to the functor of points
of the representing algebraic space. -/
theorem RepresentsBaseChange.fiberIsoClassPresheaf_iso
    {S : Scheme.{u}} {X Y : GroupoidsOver S} {f : X ⟶ Y} {U : Over S}
    {y : GroupoidsOver.slice U ⟶ Y} {Fy : AlgebraicSpace S} {fy : Fy ⟶ ofOver U}
    (h : RepresentsBaseChange f y Fy fy) :
    Nonempty
      (Functor.fiberIsoClassPresheaf
          (FiberedCategoryOver.Groupoids.p
            (TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f)) ≅
        Fy.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  sorry

end AlgebraicGeometry
