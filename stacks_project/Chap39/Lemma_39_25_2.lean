module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DescentData
namespace IsEffective

/- Lemma 39.25.2: a descent datum along a surjective finite locally free morphism is
effective if every finite set of points in one fibre of its component lies in an affine open. -/
@[stacks 0CCI]
#check (AlgebraicGeometry.Scheme.DescentData.IsEffective.ofFiniteLocallyFreeOfAffineOpen :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [IsFiniteLocallyFree f]
    (D : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f))
    (_ : ∀ (y : Y) (E : Set (D.obj PUnit.unit).left), E.Finite →
      E ⊆ ((D.obj PUnit.unit).hom ≫ f).pointsOver y →
      ∃ U : (D.obj PUnit.unit).left.affineOpens,
        E ⊆ ((U : (D.obj PUnit.unit).left.Opens) : Set (D.obj PUnit.unit).left)),
    D.IsEffective)

end IsEffective
end DescentData
end Scheme
end AlgebraicGeometry
