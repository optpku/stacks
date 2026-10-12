/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen.FiniteSet
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Comparison
import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Characterization

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DescentData
namespace IsEffective

/-- A descent datum along a surjective finite locally free morphism is effective when its
component is projective or quasi-projective, or admits an ample, relatively ample, or relatively
very ample invertible module. -/
theorem ofFiniteLocallyFreeOfProjectiveOrAmple {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [IsFiniteLocallyFree f]
    (D : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f))
    (h_geometry :
      Projective (D.obj PUnit.unit).hom ∨
        QuasiProjective (D.obj PUnit.unit).hom ∨
        Scheme.Modules.HasAmpleInvertibleModule (D.obj PUnit.unit).left ∨
        (∃ L : (D.obj PUnit.unit).left.Modules,
          RelativelyAmple (D.obj PUnit.unit).hom L) ∨
        ∃ L : (D.obj PUnit.unit).left.Modules,
          RelativelyVeryAmple (D.obj PUnit.unit).hom L) :
    D.IsEffective := sorry

end IsEffective
end DescentData
end Scheme
end AlgebraicGeometry
