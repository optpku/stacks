module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap101.Definition_101_16_2_SmoothLocal
public import stacks_project.Chap101.Lemma_101_25_5_Surjective

/-!
# Descent of smooth-local-on-source-and-target morphisms of algebraic stacks

If a morphism property of algebraic spaces is smooth local on the
source-and-target and fppf local on the target, then its lift to morphisms of
algebraic stacks descends along a surjective, flat, locally of finite
presentation base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace hasSmoothLocalAtSourceAndTarget

/-- Lemma 101.27.10: Let `P` be a property of morphisms of algebraic spaces
which is smooth local on the source-and-target and fppf local on the target.
Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let `g : Z ⟶ Y` be a
surjective, flat, locally of finite presentation morphism of algebraic stacks.
If the base change `TwoFibreProduct.snd f g` has
`hasSmoothLocalAtSourceAndTarget P`, then `f` has
`hasSmoothLocalAtSourceAndTarget P`.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g`. Flatness and local finite presentation of `g` are
the presentation conditions `existsSurjectiveSmoothSquare` for
`AlgebraicSpace.Flat` and `AlgebraicSpace.LocallyOfFinitePresentation`. -/
@[stacks 0DN6]
theorem of_twoFibreProduct_snd {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g]
    (hg_flat : existsSurjectiveSmoothSquare
      (@AlgebraicSpace.Flat S : MorphismProperty (AlgebraicSpace S)) g)
    (hg_lfp : existsSurjectiveSmoothSquare
      (@AlgebraicSpace.LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) g)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    (hP : hasSmoothLocalAtSourceAndTarget P
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) :
    hasSmoothLocalAtSourceAndTarget P f :=
  sorry

/-- The lift of a morphism property of algebraic spaces that is smooth local on
the source-and-target and fppf local on the target descends along the second
projection of a bilimit `PseudoPullbackCone` against a surjective, flat,
locally of finite presentation morphism of algebraic stacks. -/
theorem of_isBilimit_snd {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] {f : X ⟶ Y} {g : Z ⟶ Y} [Surjective g]
    (hg_flat : existsSurjectiveSmoothSquare
      (@AlgebraicSpace.Flat S : MorphismProperty (AlgebraicSpace S)) g)
    (hg_lfp : existsSurjectiveSmoothSquare
      (@AlgebraicSpace.LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) g)
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    (hP : hasSmoothLocalAtSourceAndTarget P c.snd) :
    hasSmoothLocalAtSourceAndTarget P f :=
  sorry

end hasSmoothLocalAtSourceAndTarget

end AlgebraicGeometry.AlgebraicStack
