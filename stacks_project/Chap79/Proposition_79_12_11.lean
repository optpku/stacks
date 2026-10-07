module

public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap79.«79_12_0_2»
public import stacks_project.Chap79.Lemma_79_12_1_Hom

/-!
# The finite part of a separated locally finite-type morphism

If `f : X ⟶ Y` is separated and locally of finite type, then the finite-part
functor `(X/Y)_fin` is an algebraic space and the structure morphism
`(X/Y)_fin ⟶ Y` is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Proposition 79.12.11 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism
of algebraic spaces over `S` which is separated and locally of finite type.
Then `(X/Y)_fin` is an algebraic space. -/
@[stacks 04QH, instance]
instance instIsAlgebraicSpace (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] :
    IsAlgebraicSpace (finitePart f) :=
  sorry

/-- The algebraic space associated to the finite-part functor `(X/Y)_fin`. -/
def space (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] : AlgebraicSpace S :=
  ofIsAlgebraicSpace (finitePart f)

/-- The functor of points of `space f` is `finitePart f`. -/
theorem space_functorOfPoints (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] :
    (space f).functorOfPoints = finitePart f :=
  sorry

/-- The structure morphism `(X/Y)_fin ⟶ Y`, as a morphism of algebraic spaces. -/
def spaceHom (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] : space f ⟶ Y :=
  toY f

/-- `spaceHom f` is the functor-of-points morphism `toY f`. -/
theorem spaceHom_eq (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] :
    spaceHom f = toY f :=
  sorry

/-- Proposition 79.12.11 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism
of algebraic spaces over `S` which is separated and locally of finite type.
Then the morphism `(X/Y)_fin ⟶ Y` is étale. -/
@[stacks 04QH, instance]
instance instEtale_spaceHom (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] :
    Etale (spaceHom f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
