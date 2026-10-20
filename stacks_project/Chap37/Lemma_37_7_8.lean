/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyUnramified.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.Restriction
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.7.8 (1): a formally unramified morphism remains formally unramified after
restriction to compatible open subschemes. -/
@[stacks 04FA] #check
  (@AlgebraicGeometry.FormallyUnramified.resLE :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V)
      [AlgebraicGeometry.FormallyUnramified f],
      AlgebraicGeometry.FormallyUnramified (f.resLE V U e))

/- Lemma 37.7.8 (2): the universal first-order thickening of a compatible open is the
corresponding open in the original universal first-order thickening. -/
@[stacks 04FA] #check
  (@AlgebraicGeometry.Thickening.IsUniversalFirstOrder.restrict_spec :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (T : AlgebraicGeometry.Thickening.Over X)
      (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U)
      [AlgebraicGeometry.FormallyUnramified T.left.hom]
      [AlgebraicGeometry.Thickening.IsUniversalFirstOrder T],
      T.hom.left ⁻¹ᵁ (AlgebraicGeometry.IsThickening.opensEquiv T.hom.left V) = V ∧
        AlgebraicGeometry.Thickening.IsUniversalFirstOrder
          (AlgebraicGeometry.Thickening.Over.restrict T U V hV))

/- Lemma 37.7.8 (3): the canonical comparison identifies the restricted conormal sheaf with
the conormal sheaf of the restricted morphism. -/
@[stacks 04FA] #check
  (@AlgebraicGeometry.Thickening.IsUniversalFirstOrder.restrictConormalMap_isIso :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (T : AlgebraicGeometry.Thickening.Over X)
      (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U)
      [AlgebraicGeometry.FormallyUnramified T.left.hom]
      [AlgebraicGeometry.Thickening.IsUniversalFirstOrder T],
      IsIso (AlgebraicGeometry.Scheme.Hom.Conormal.map
        (AlgebraicGeometry.Thickening.Over.restrictSquare T U V hV).toCommSq))
