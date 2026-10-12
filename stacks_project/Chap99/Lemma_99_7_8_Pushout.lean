/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import stacks_project.Chap99.«99_7_1_1_Functor»

/-!
# Restriction of quotient functors along a pushout square

A functor `G : (SchemesOver B)ᵒᵖ ⥤ Type v` sends a commutative square of schemes
over `B` to a cospan of restriction maps. The comparison
`pushoutComparison` is the induced map into the Type-valued pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The two restrictions of `G` along a commutative square in `SchemesOver B`
agree on `G.obj (op Z)`. -/
theorem pushoutComparison_comm (G : (SchemesOver B)ᵒᵖ ⥤ Type v)
    {Z Z' Y Y' : SchemesOver B} {i : Z ⟶ Z'} {g : Z ⟶ Y}
    {inl : Z' ⟶ Y'} {inr : Y ⟶ Y'} (h : i ≫ inl = g ≫ inr) :
    G.map inr.op ≫ G.map g.op = G.map inl.op ≫ G.map i.op :=
  sorry

/-- The natural restriction map
`G.obj (op Y') ⟶ pullback (G.map g.op) (G.map i.op)` associated to a
commutative square of schemes over `B`. -/
def pushoutComparison (G : (SchemesOver B)ᵒᵖ ⥤ Type v)
    {Z Z' Y Y' : SchemesOver B} {i : Z ⟶ Z'} {g : Z ⟶ Y}
    {inl : Z' ⟶ Y'} {inr : Y ⟶ Y'} (h : i ≫ inl = g ≫ inr) :
    G.obj (op Y') ⟶ pullback (G.map g.op) (G.map i.op) :=
  pullback.lift (G.map inr.op) (G.map inl.op)
    (((G.map_comp inr.op g.op).symm.trans
        (congrArg G.map (congrArg (fun k ↦ k.op) h.symm))).trans
      (G.map_comp inl.op i.op))

/-- The first projection of `pushoutComparison` is restriction along `inr`. -/
theorem pushoutComparison_fst (G : (SchemesOver B)ᵒᵖ ⥤ Type v)
    {Z Z' Y Y' : SchemesOver B} {i : Z ⟶ Z'} {g : Z ⟶ Y}
    {inl : Z' ⟶ Y'} {inr : Y ⟶ Y'} (h : i ≫ inl = g ≫ inr) :
    pushoutComparison G h ≫ pullback.fst _ _ = G.map inr.op :=
  sorry

/-- The second projection of `pushoutComparison` is restriction along `inl`. -/
theorem pushoutComparison_snd (G : (SchemesOver B)ᵒᵖ ⥤ Type v)
    {Z Z' Y Y' : SchemesOver B} {i : Z ⟶ Z'} {g : Z ⟶ Y}
    {inl : Z' ⟶ Y'} {inr : Y ⟶ Y'} (h : i ≫ inl = g ≫ inr) :
    pushoutComparison G h ≫ pullback.snd _ _ = G.map inl.op :=
  sorry

/-- `pushoutComparison` pairs the restrictions of `G` along `inr` and `inl`. -/
theorem pushoutComparison_spec (G : (SchemesOver B)ᵒᵖ ⥤ Type v)
    {Z Z' Y Y' : SchemesOver B} {i : Z ⟶ Z'} {g : Z ⟶ Y}
    {inl : Z' ⟶ Y'} {inr : Y ⟶ Y'} (h : i ≫ inl = g ≫ inr) :
    pushoutComparison G h ≫ pullback.fst _ _ = G.map inr.op ∧
      pushoutComparison G h ≫ pullback.snd _ _ = G.map inl.op :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
