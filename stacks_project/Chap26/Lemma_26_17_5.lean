/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.ResidueField

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open Scheme.Pullback

universe u

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/- Lemma 26.17.5 (1): points of a scheme pullback are compatible triples
together with a prime of the tensor product of residue fields. -/
@[stacks 01JT]
#check (Scheme.Pullback.carrierEquiv :
  (pullback f g : Scheme) ≃
    Σ T : Scheme.Pullback.Triplet f g, Spec T.tensor)

/- Lemma 26.17.5 (2): the associated-prime residue-field comparison is an
isomorphism. -/
@[stacks 01JT] #check Scheme.Pullback.ofPointTensor_SpecTensorTo
@[stacks 01JT] #check Scheme.Pullback.SpecOfPoint.eq_map_closedPoint
@[stacks 01JT] #check Scheme.Pullback.SpecOfPoint.residueFieldMap
#check Scheme.Pullback.SpecOfPoint.algebraMap_residueFieldMap
@[stacks 01JT] #check Scheme.Pullback.SpecOfPoint.residueFieldMap_isIso
#check Scheme.Pullback.SpecOfPoint.residueFieldMap_bijective
#check Scheme.Pullback.SpecOfPoint.residueFieldMap_spec
