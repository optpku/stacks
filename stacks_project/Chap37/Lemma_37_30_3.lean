/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FinitePresentation

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace FinitePresentation

/- Lemma 37.30.3: every level set of the target-indexed fibre-dimension
function of a finite-presentation morphism of schemes is locally constructible. -/
@[stacks 05F9] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.fiberDimension_levelSet_isLocallyConstructible :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Scheme.Hom.FinitePresentation f]
      (n : WithBot ℕ∞),
      Topology.IsLocallyConstructible {y : Y | f.fiberDimension y = n})

end FinitePresentation
end AlgebraicGeometry.Scheme.Hom
