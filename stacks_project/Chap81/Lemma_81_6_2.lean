module

public import stacks_project.Chap81.Lemma_81_6_2_Pushout
public import stacks_project.Chap81.Lemma_81_6_2_StructureSheaf
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening
open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 81.6.2 (1): a thickening and an affine morphism of algebraic spaces over a
scheme `S` have a pushout in the category of algebraic spaces over `S`. -/
@[stacks 07VX] #check
  (instHasPushout :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f], HasPushout i f)

/- Lemma 81.6.2 (2): the canonical morphism from the target of the affine morphism
to the pushout is a thickening. -/
@[stacks 07VX] #check
  (instInrIsThickening :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f], IsThickening (pushout.inr i f))

/- Lemma 81.6.2 (3): on the identified small étale sites, the structure sheaf of the
pushout is the fibre product of `𝒪_Y` and `f'_* 𝒪_{X'}` over `f_* 𝒪_X`. -/
@[stacks 07VX] #check
  (structureSheaf_isPullback :
    ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
      {i : X ⟶ X'} {f : X ⟶ Y} {i' : X' ⟶ Y'} {g : Y ⟶ Y'}
      [IsThickening i] [Affine f] (h : IsPushout i f i' g),
      IsStructureSheafPullback i f i' g h.toCommSq)
