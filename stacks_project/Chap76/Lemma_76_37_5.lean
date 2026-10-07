module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_17_3_SchemeTheoreticDensity
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Extending open immersions from a dense open of algebraic spaces

A morphism of algebraic spaces that is separated, locally of finite type, and
flat is an open immersion if it is an isomorphism over a quasi-compact
scheme-theoretically dense open of the target.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion

/-- Lemma 76.37.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `ι : V ⟶ Y` be an open immersion (an open
subspace of `Y`). Assume `f` is separated, locally of finite type, and flat,
`ι` is quasi-compact and scheme-theoretically dense, and the restriction
`openInverseImageTo f ι : openInverseImage f ι ⟶ V` is an isomorphism. Then
`f` is an open immersion. -/
@[stacks 0879]
theorem of_isIso_restrict_of_flat {S : Scheme.{u}} {X Y V : AlgebraicSpace S}
    (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] [Flat f] (ι : V ⟶ Y)
    [IsOpenImmersion ι] [QuasiCompact ι] [IsSchemeTheoreticallyDense ι]
    [IsIso (openInverseImageTo f ι)] :
    IsOpenImmersion f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion
