/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.GeometricallyUnibranch

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 37.37.3 (1): if a composite `f ≫ g` is étale at `x`, the integral
scheme `Y` is geometrically unibranch at `f x`, and a generalization of `x`
maps to the generic point of `Y`, then `f` is étale at `x`. -/
@[stacks 0GSA]
#check (AlgebraicGeometry.Scheme.Hom.EtaleAt.left_of_comp_of_specializes_genericPoint :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral Y] (x x' : X),
    Y.isGeometricallyUnibranchAt (f x) → x' ⤳ x → f x' = genericPoint Y →
      (f ≫ g).EtaleAt x → f.EtaleAt x)

/- Lemma 37.37.3 (2): if a composite `f ≫ g` is étale at `x`, the integral
scheme `Y` is geometrically unibranch at `f x`, and a generalization of `x`
maps to the generic point of `Y`, then `g` is étale at `f x`. -/
@[stacks 0GSA]
#check (AlgebraicGeometry.Scheme.Hom.EtaleAt.right_of_comp_of_specializes_genericPoint :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral Y] (x x' : X),
    Y.isGeometricallyUnibranchAt (f x) → x' ⤳ x → f x' = genericPoint Y →
      (f ≫ g).EtaleAt x → g.EtaleAt (f x))

end AlgebraicGeometry
