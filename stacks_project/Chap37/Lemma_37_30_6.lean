/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.ProperFlat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.FinitePresentation

/- Lemma 37.30.6: the target-indexed fibre-dimension function of a proper, flat
finite-presentation morphism of schemes is locally constant. -/
@[stacks 0D4J] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.isLocallyConstant_fiberDimension :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [Flat f]
      [Scheme.Hom.FinitePresentation f], IsLocallyConstant f.fiberDimension)

end AlgebraicGeometry.Scheme.Hom.FinitePresentation
