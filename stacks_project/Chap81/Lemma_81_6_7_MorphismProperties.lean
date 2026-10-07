module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap81.Lemma_81_6_3_Gluing

/-!
# Morphism properties of algebraic-space pushout gluing

Morphisms from algebraic spaces obtained by pushout gluing have the standard
local morphism properties exactly when both component morphisms do.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing

variable {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
variable (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]

/-- An algebraic space obtained by pushout gluing is locally of finite type over
`pushout i f` exactly when both components are locally of finite type. -/
theorem locallyOfFiniteType_iff
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    LocallyOfFiniteType ((Gluing.glue i f).obj P).hom ↔
      LocallyOfFiniteType P.fst.hom ∧ LocallyOfFiniteType P.snd.hom :=
  sorry

/-- An algebraic space obtained by pushout gluing is flat over `pushout i f`
exactly when both components are flat. -/
theorem flat_iff (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    Flat ((Gluing.glue i f).obj P).hom ↔ Flat P.fst.hom ∧ Flat P.snd.hom :=
  sorry

/-- An algebraic space obtained by pushout gluing is flat and locally of finite
presentation exactly when both components have these two properties. -/
theorem flatLocallyOfFinitePresentation_iff
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    (Flat ((Gluing.glue i f).obj P).hom ∧
        LocallyOfFinitePresentation ((Gluing.glue i f).obj P).hom) ↔
      (Flat P.fst.hom ∧ LocallyOfFinitePresentation P.fst.hom) ∧
        (Flat P.snd.hom ∧ LocallyOfFinitePresentation P.snd.hom) :=
  sorry

/-- An algebraic space obtained by pushout gluing is smooth over `pushout i f`
exactly when both components are smooth. -/
theorem smooth_iff (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    Smooth ((Gluing.glue i f).obj P).hom ↔ Smooth P.fst.hom ∧ Smooth P.snd.hom :=
  sorry

/-- An algebraic space obtained by pushout gluing is étale over `pushout i f`
exactly when both components are étale. -/
theorem etale_iff (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    Etale ((Gluing.glue i f).obj P).hom ↔ Etale P.fst.hom ∧ Etale P.snd.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing
