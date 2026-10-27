/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism

/-!
# Open subspaces cut out by opens of points

An open of `Points X` determines an open subspace of an algebraic space `X` as
the subfunctor of maps into `X` whose image of points lands in that open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/- The morphism `ofOver U.unop ⟶ X` associated to a section of the functor of points. -/
#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.homOfPointsSection :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : (Over S)ᵒᵖ},
    X.functorOfPoints.obj U → (ofOver U.unop ⟶ X))

/-- The subfunctor of maps into `X` whose image of points lands in `W`. -/
abbrev ofOpensSubfunctor (W : Opens (Points X)) : Subfunctor X.functorOfPoints :=
  Construction.subfunctor X W

/-- The algebraic space underlying the open subspace cut out by `W`. -/
abbrev ofOpensSpace (W : Opens (Points X)) : AlgebraicSpace S :=
  Construction.space X W

/-- The inclusion of the open subspace cut out by `W` into `X`. -/
abbrev ofOpensι (W : Opens (Points X)) : ofOpensSpace W ⟶ X :=
  Construction.ι X W

/-- The inclusion of the open subspace cut out by `W` is an open immersion. -/
instance instIsOpenImmersion_ofOpensι (W : Opens (Points X)) :
    IsOpenImmersion (ofOpensι W) :=
  Construction.inclusion_isOpenImmersion X W

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.fromOpens :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    Opens (Points X) → OpenSubspace X)

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace
