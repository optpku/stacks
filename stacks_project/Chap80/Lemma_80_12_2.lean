/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSheaf
import StacksCheckRecall

/-!
# Algebraic spaces from étale sheaves with an algebraic-space étale atlas

An étale sheaf on schemes over `S` that admits a representable, surjective, and
étale map from an algebraic space is itself an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 80.12.2: denote the common underlying category of `Sch_fppf` and
`Sch_étale` by `Sch_α` (see Topologies, Remark 34.11.1), recovered here as the
common `Over S` of `Scheme.etaleTopology` and `Scheme.fppfTopology`. Let `S` be a
scheme. Let `F : (Over S)ᵒᵖ ⥤ Type u` be a presheaf. If `F` is a sheaf for the
étale topology, and there is an algebraic space `U` over `S` with a map `U ⟶ F`
which is representable by algebraic spaces, surjective, and étale, then `F` is an
algebraic space in the sense of Algebraic Spaces, Definition 65.6.1. -/
@[stacks 0BH4] #check
  (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_etaleSheaf_etale_surjective :
    ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
      (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
      {U : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace U] (a : U ⟶ F)
      (ha : relativeAlgebraicSpaces
        (@Surjective S ⊓ @Etale S : MorphismProperty (AlgebraicSpace S)) a),
      IsAlgebraicSpace F)

end AlgebraicGeometry.AlgebraicSpace
