/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.GenericPoints

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.17.1: finite residue-field extensions at generic points imply finite-type
quasi-finiteness at every point over a Noetherian target point of dimension at most one. -/
@[stacks 0AB6] #check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.at_of_finiteGenericResidues :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.LocallyOfFiniteType f] (y : Y),
      IsNoetherianRing (Y.presheaf.stalk y) →
        ringKrullDim (Y.presheaf.stalk y) ≤ 1 →
          AlgebraicGeometry.Scheme.Hom.GenericPoints.finiteResidues f →
            ∀ x : X, f x = y →
              AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt f x)

/- Algebraic residue-field extensions at generic points give the same conclusion. -/
#check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.at_of_algebraicGenericResidues :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.LocallyOfFiniteType f] (y : Y),
      IsNoetherianRing (Y.presheaf.stalk y) →
        ringKrullDim (Y.presheaf.stalk y) ≤ 1 →
          AlgebraicGeometry.Scheme.Hom.GenericPoints.algebraicResidues f →
            ∀ x : X, f x = y →
              AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt f x)

/- Finite residue-field extensions at generic points specializing to the selected target point
give the same conclusion. -/
#check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.at_of_finiteGenericResiduesOver :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.LocallyOfFiniteType f] (y : Y),
      IsNoetherianRing (Y.presheaf.stalk y) →
        ringKrullDim (Y.presheaf.stalk y) ≤ 1 →
          AlgebraicGeometry.Scheme.Hom.GenericPoints.finiteResiduesOver f y →
            ∀ x : X, f x = y →
              AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt f x)

/- Algebraic residue-field extensions at generic points specializing to the selected target point
give the same conclusion. -/
#check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.at_of_algebraicGenericResiduesOver :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.LocallyOfFiniteType f] (y : Y),
      IsNoetherianRing (Y.presheaf.stalk y) →
        ringKrullDim (Y.presheaf.stalk y) ≤ 1 →
          AlgebraicGeometry.Scheme.Hom.GenericPoints.algebraicResiduesOver f y →
            ∀ x : X, f x = y →
              AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt f x)

/- Finite-type quasi-finiteness at every generic point gives the same conclusion. -/
#check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.at_of_genericPoints :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.LocallyOfFiniteType f] (y : Y),
      IsNoetherianRing (Y.presheaf.stalk y) →
        ringKrullDim (Y.presheaf.stalk y) ≤ 1 →
          AlgebraicGeometry.Scheme.Hom.GenericPoints.quasiFinite f →
            ∀ x : X, f x = y →
              AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt f x)

/- A dense finite-type quasi-finite locus on a locally Noetherian target gives the same
conclusion. -/
#check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.at_of_denseLocus :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      [AlgebraicGeometry.IsLocallyNoetherian Y] (y : Y),
      IsNoetherianRing (Y.presheaf.stalk y) →
        ringKrullDim (Y.presheaf.stalk y) ≤ 1 →
          AlgebraicGeometry.Scheme.Hom.QuasiFinite.hasDenseLocus f →
            ∀ x : X, f x = y →
              AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt f x)

end
