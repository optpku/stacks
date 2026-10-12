/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_95_1
public import stacks_project.Chap59.Definition_59_96_1
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Lemma 59.96.2 (1): if `K` is a field and `f : X ⟶ Y` is a morphism of finite type
schemes over `K`, then `Hom.cohomologicalDimension f.left ≠ ⊤`. -/
@[stacks 0F10]
theorem Hom.cohomologicalDimension_ne_top
    {K : Type u} [Field K] {X Y : SchemeOverField K} [Algebraic X] [Algebraic Y]
    (f : X ⟶ Y) [QuasiCompact f.left] [QuasiSeparated f.left]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})] :
    Hom.cohomologicalDimension f.left ≠ ⊤ := sorry

/-- Lemma 59.96.2 (2): if `K` is a field with
`cohomologicalDimension (Spec (CommRingCat.of K)) ≠ ⊤`, then every finite type
scheme `X` over `K` has `cohomologicalDimension X.left ≠ ⊤`. -/
@[stacks 0F10]
theorem cohomologicalDimension_ne_top
    {K : Type u} [Field K] {X : SchemeOverField K} [Algebraic X]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})]
    (hK : cohomologicalDimension (Spec (CommRingCat.of K)) ≠ ⊤) :
    cohomologicalDimension X.left ≠ ⊤ := sorry

end AlgebraicGeometry.Scheme

end
