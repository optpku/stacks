/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.Excision

/-! # Fibres of finite-family excision -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Each coordinate of finite-family excision along affine elementary étale
neighbourhoods has distinguished residue-field fibre isomorphic to the fibre
of the original morphism at the corresponding closed point. -/
theorem fiberOver_excisionFamily {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx) (i : ι) :
    Nonempty
      (fieldFiber
          ((excisionFamilyFunctor X x hx hx_inj U hU_affine hU_elem hU).obj Y i).obj.hom
          (FieldValuedPoint.ofScheme
            (Scheme.FieldValuedPoint.residuePoint (U i).point)) ≅
        fieldFiber Y.obj.hom (FieldValuedPoint.residuePoint (x i))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
