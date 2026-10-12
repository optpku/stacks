/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.LocalEquality
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Unramified

/- Proposition 41.6.3: Two morphisms from a connected scheme to an unramified separated
scheme over a common base are equal if they agree at one point and induce the same map on
residue fields there. -/
@[stacks 024V] #check
  (AlgebraicGeometry.Unramified.eq_of_residueFieldMap_eq :
    ∀ {S X Y : Scheme.{u}} (π : X ⟶ S)
      [Unramified π] [IsSeparated π] (p : Y ⟶ S) [ConnectedSpace Y]
      (f g : Y ⟶ X) (hf_over : f ≫ π = p) (hg_over : g ≫ π = p)
      (y : Y) (x : X) (hfy : f y = x) (hgy : g y = x)
      (hκ : (Scheme.residueFieldCongr hfy).inv ≫ f.residueFieldMap y =
        (Scheme.residueFieldCongr hgy).inv ≫ g.residueFieldMap y),
      f = g)

end AlgebraicGeometry.Unramified
