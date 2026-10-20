module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
import StacksCheckRecall

@[expose] public section

/-!
# Definition 31.12.1

@stack 0AVU

The canonical owner is `AlgebraicGeometry.Scheme.Modules.IsReflexive`, together with the dual,
reflexive-hull, and canonical-map API in
`ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive`.
-/

universe u

#check (@AlgebraicGeometry.Scheme.Modules.dual :
  {X : AlgebraicGeometry.Scheme.{u}} →
    [CategoryTheory.MonoidalCategory X.Modules] →
      [CategoryTheory.MonoidalClosed X.Modules] → X.Modules → X.Modules)

#check (@AlgebraicGeometry.Scheme.Modules.reflexiveHull :
  {X : AlgebraicGeometry.Scheme.{u}} →
    [CategoryTheory.MonoidalCategory X.Modules] →
      [CategoryTheory.MonoidalClosed X.Modules] → X.Modules → X.Modules)

#check (@AlgebraicGeometry.Scheme.Modules.toReflexiveHull :
  {X : AlgebraicGeometry.Scheme.{u}} →
    [CategoryTheory.MonoidalCategory X.Modules] →
      [CategoryTheory.MonoidalClosed X.Modules] →
        [CategoryTheory.BraidedCategory X.Modules] →
          (ℱ : X.Modules) →
            ℱ ⟶ AlgebraicGeometry.Scheme.Modules.reflexiveHull ℱ)

/- Definition 31.12.1: A coherent module sheaf on an integral locally Noetherian scheme is
reflexive when its canonical morphism to its double dual is an isomorphism. -/
@[stacks 0AVU]
#check (@AlgebraicGeometry.Scheme.Modules.IsReflexive :
  {X : AlgebraicGeometry.Scheme.{u}} →
    [CategoryTheory.MonoidalCategory X.Modules] →
      [CategoryTheory.MonoidalClosed X.Modules] →
        [CategoryTheory.BraidedCategory X.Modules] → X.Modules → Prop)
