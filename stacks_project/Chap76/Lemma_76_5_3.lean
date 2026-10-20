/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap76.Lemma_76_5_3_Map
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Functorial
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {Z X Z' X' : AlgebraicSpace S}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
variable [IsImmersion i] [IsImmersion i']
variable (sq : CommSq f i i' g)

/- Lemma 76.5.3: Let `S` be a scheme. A commutative diagram of algebraic spaces
over `S` whose horizontal arrows `i : Z ⟶ X` and `i' : Z' ⟶ X'` are immersions
induces a canonical morphism of `𝒪_Z`-modules
`(Modules.pullback f).obj (Hom.conormalSheaf i') ⟶ Hom.conormalSheaf i`. -/
@[stacks 04CP]
#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.map sq :
    (Modules.pullback f).obj (Hom.conormalSheaf i') ⟶ Hom.conormalSheaf i)

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.map_spec sq :
    AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.IsMap sq
      (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.map sq))
