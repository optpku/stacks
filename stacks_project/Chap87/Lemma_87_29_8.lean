/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineFiniteType
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 87.29.8: Let `S` be a scheme and `f : X ⟶ Y` a morphism of affine
formal algebraic spaces with `Y` countably indexed. The following are equivalent:
`f` is locally of finite type, `f` is of finite type, and `f` corresponds to a
morphism `B →+* A` of `WAdm^count` satisfying the equivalent conditions of
Lemma 87.29.6. The ring condition used here is that the continuous map is taut
and topologically of finite type, which is condition (c) of that lemma. The
correspondence includes countably indexed weakly admissible presentations of
both spaces and compatibility of the induced `spfMap` with `f`. -/
@[stacks 0ANV] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.locallyOfFiniteType_tfae :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
      [AlgebraicGeometry.AffineFormalAlgebraicSpace.IsAffine X]
      [AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine Y]
      [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] (f : X ⟶ Y),
      List.TFAE [FormalAlgebraicSpace.LocallyOfFiniteType f, FiniteType f,
        AlgebraicGeometry.AffineFormalAlgebraicSpace.exists_spfMap_isTaut_and_topologicallyOfFiniteType f])
