/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Group.TangentSpace

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Pullback

noncomputable section

universe u

/- Lemma 39.6.4: for a group scheme over `S`, the tangent map of multiplication at the pair of
identity points sends the tangent vector determined by `(v, w)` to `v + w`. -/
@[stacks 0BF5]
#check (AlgebraicGeometry.Scheme.GroupTangent.mul_apply :
  ∀ {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S)
    (v w : tangentSpaceAt G.hom (η[G].left s)),
    let unitPairTangent :=
      cast (AlgebraicGeometry.Scheme.GroupTangent.unitPair_tangent_eq G s)
        (pullbackTangentCopairing G.hom G.hom
          (η[G].left s) (η[G].left s) rfl
          (AlgebraicGeometry.Scheme.GroupTangent.unit_residueFieldMap_bijective G s)
          (AlgebraicGeometry.Scheme.GroupTangent.unit_residueFieldMap_bijective G s)
          (v, w))
    let mulTangent :=
      cast (AlgebraicGeometry.Scheme.GroupTangent.mul_unitPair_tangentTarget_eq G s)
        (relativeTangentMapAt μ[G].left G.hom ((lift η[G] η[G]).left s)
          (AlgebraicGeometry.Scheme.GroupTangent.mul_residueFieldMap_bijective G s)
          (cast (AlgebraicGeometry.Scheme.GroupTangent.mul_unitPair_tangentSource_eq G s)
            unitPairTangent))
    mulTangent = v + w)
