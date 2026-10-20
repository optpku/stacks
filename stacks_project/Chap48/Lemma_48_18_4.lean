/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Fiber
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Scheme.Hom
open Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Compactification
namespace Of
namespace UpperShriek

/- Lemma 48.18.4 -/
@[stacks 0BZZ] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.fiberPullback_isDualizingComplex :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
      (P : Of Y.obj.left (Over.mk f.hom.left))
      (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) (y : Y.obj.left),
      IsDualizingComplex
        ((DerivedQCoh.pullback (fiberι f.hom.left y)).obj
          (dualizingObject f P A)).obj)

end UpperShriek
end Of
end Compactification
end Scheme
end AlgebraicGeometry
