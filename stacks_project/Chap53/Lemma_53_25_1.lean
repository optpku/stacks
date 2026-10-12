/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.DualizingPullback

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.25.1: for a morphism of proper reduced Gorenstein one-dimensional schemes over a
field satisfying the structure-sheaf and first higher-direct-image vanishing conditions, and
with a globally generated tensor power having vanishing first cohomology, the pullback of the
target curve dualizing module is isomorphic to the source curve dualizing module. -/
@[stacks 0E7P] #check
  (AlgebraicGeometry.SchemeOverField.curveDualizingModule_pullback_isomorphic :
    ∀ {k : Type u} [Field k] (X Y : SchemeOverField k) (c : X ⟶ Y)
      [IsProper X.hom] [IsProper Y.hom] [IsReduced X.left] [IsReduced Y.left]
      [Scheme.Gorenstein X.left] [Scheme.Gorenstein Y.left]
      [EquidimensionalSpace X.left] [EquidimensionalSpace Y.left]
      [Fact (topologicalKrullDim X.left = 1)] [Fact (topologicalKrullDim Y.left = 1)]
      (h_structure :
        IsIso (RingedSpace.Hom.commRingSheafPushforwardMap c.left.toShHom))
      (h_R1 :
        IsZero (RingedSpace.Hom.higherDirectImageModule c.left.toShHom
          (SheafOfModules.unit X.left.ringCatSheaf) 1)),
    (∃ m : ℤ,
        IsZero (Scheme.Hom.cohomology X.hom
          (Scheme.Modules.tensorPowerInt (curveDualizingModule X.hom) m) 1) ∧
          SheafOfModules.IsGloballyGenerated
            (Scheme.Modules.tensorPowerInt (curveDualizingModule X.hom) m)) →
      IsIsomorphic
        ((Scheme.Modules.pullback c.left).obj (curveDualizingModule Y.hom))
        (curveDualizingModule X.hom))

end AlgebraicGeometry.SchemeOverField
