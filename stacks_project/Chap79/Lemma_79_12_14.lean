module

public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Lemma_67_28_5
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap79.Proposition_79_12_11

/-!
# The finite part of a separated flat locally finite-presentation morphism

If `f : X ⟶ Y` is separated, flat, and locally of finite presentation, then
the structure morphism `(X/Y)_fin ⟶ Y` is separated, representable, and
étale, and if `Y` is a scheme then `(X/Y)_fin` is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 79.12.14 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is separated, flat, and locally of finite
presentation. Then the structure morphism `spaceHom f : space f ⟶ Y`, i.e.
`(X/Y)_fin ⟶ Y`, is separated, representable, and étale. The étale clause is
`instEtale_spaceHom`. -/
@[stacks 04RI, instance]
instance instSeparated_spaceHom (f : X ⟶ Y) [Separated f] [Flat f]
    [LocallyOfFinitePresentation f] : Separated (spaceHom f) :=
  sorry

/-- The structure morphism `spaceHom f : space f ⟶ Y` is representable. -/
theorem relativelyRepresentable_spaceHom (f : X ⟶ Y) [Separated f] [Flat f]
    [LocallyOfFinitePresentation f] :
    yoneda.relativelyRepresentable (spaceHom f) :=
  sorry

/-- Lemma 79.12.14 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is separated, flat, and locally of finite
presentation. If `Y` is a scheme, then `(X/Y)_fin` is a scheme. -/
@[stacks 04RI, instance]
instance instIsScheme_space (f : X ⟶ Y) [Separated f] [Flat f]
    [LocallyOfFinitePresentation f] [IsScheme Y] : IsScheme (space f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
