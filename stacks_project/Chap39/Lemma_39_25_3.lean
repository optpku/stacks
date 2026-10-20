/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity.FiniteLocallyFree.Ample
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DescentData
namespace IsEffective

/- Lemma 39.25.3: a descent datum along a surjective finite locally free morphism is
effective when its component is projective or quasi-projective, or carries an ample,
relatively ample, or relatively very ample invertible module. -/
@[stacks 0CCJ] #check
  (AlgebraicGeometry.Scheme.DescentData.IsEffective.ofFiniteLocallyFreeOfProjectiveOrAmple :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [IsFiniteLocallyFree f]
      (D : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f)),
      (Projective (D.obj PUnit.unit).hom ∨
          QuasiProjective (D.obj PUnit.unit).hom ∨
          Scheme.Modules.HasAmpleInvertibleModule (D.obj PUnit.unit).left ∨
          (∃ L : (D.obj PUnit.unit).left.Modules,
            RelativelyAmple (D.obj PUnit.unit).hom L) ∨
          ∃ L : (D.obj PUnit.unit).left.Modules,
            RelativelyVeryAmple (D.obj PUnit.unit).hom L) →
        D.IsEffective)

end IsEffective
end DescentData
end Scheme
end AlgebraicGeometry
