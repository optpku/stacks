/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.DualNumber
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped DualNumber

universe u

/- 33.16.1.1: the canonical residue-field point maps and dual-number maps form the solid
commutative square in the tangent-space diagram. -/
@[stacks 0B2A] #check
  (AlgebraicGeometry.Scheme.Hom.dualNumberPointCommSq :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X),
      CommSq (X.fromSpecResidueField x)
        (AlgebraicGeometry.Scheme.Hom.dualNumberPointInclusion x) f
        (AlgebraicGeometry.Scheme.Hom.dualNumberToBasePoint f x ≫
          S.fromSpecResidueField (f x)))

#check
  (AlgebraicGeometry.Scheme.Hom.dualNumberPointInclusion_comp_toBasePoint :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X),
      AlgebraicGeometry.Scheme.Hom.dualNumberPointInclusion x ≫
          AlgebraicGeometry.Scheme.Hom.dualNumberToBasePoint f x =
        AlgebraicGeometry.Spec.map (f.residueFieldMap x))
