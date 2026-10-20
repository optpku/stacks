/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap89.«89_3_0_1»
public import stacks_project.Chap89.Lemma_89_3_3_Fiber

/-!
# Fibres of morphisms corresponding under family excision
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 89.3.3: let `X`, `x i`, `U i ⟶ X`, `u i` be as in 89.3.0.1. If
`f : Y ⟶ X` corresponds to `g i : Y i ⟶ U i` under `F`, then
`Y_{x i} ≅ (Y i)_{u i}` as algebraic spaces. Here `F` is
`excisionFamilyFunctor`, the morphism `g i` is the structure morphism of
`(excisionFamilyFunctor X x hx U).obj Y i`, and the fibres are the
scheme-theoretic algebraic-space fibres `fieldFiber` over the residue-field
points of `x i` and of `u i`. The identification is induced by
`Spec(κ(u i)) ⟶ Spec(κ(x i))` being an isomorphism, which holds because
each `U i` is elementary. -/
@[stacks 0BHD]
theorem fiberOver_excisionFamily {ι : Type} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (hU : ∀ i, (U i).IsElementary)
    (Y : IsoOverClosedPoints X x hx) (i : ι) :
    Nonempty
      (fieldFiber ((excisionFamilyFunctor X x hx U).obj Y i).obj.hom
          (FieldValuedPoint.ofScheme
            (Scheme.FieldValuedPoint.residuePoint (U i).point)) ≅
        fieldFiber Y.obj.hom (FieldValuedPoint.residuePoint (x i))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
