module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ConnectedComponents

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace FiniteType

/- Lemma 37.28.5: for a finite-type morphism, the geometric connected-fibre
component count is constant on a nonempty open of the reduced closure of any point. -/
@[stacks 055H] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_geometricFiberComponentCount_eq :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] (y : Y),
      ∃ V : (PointClosure.scheme y).Opens, Nonempty V ∧
        ∃ c : ℕ∞, ∀ z : PointClosure.scheme y, z ∈ V →
          f.geometricFiberComponentCount (PointClosure.ι y z) = c)

end FiniteType
end Hom
end Scheme
end AlgebraicGeometry
