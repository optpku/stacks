/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Envelope
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BivariantClass

/- Lemma 42.35.6: a degree-`p` bivariant class on the pullback of `f` along an
envelope `g` descends uniquely when its two restrictions to the Čech self-intersection
agree. -/
@[stacks 0GUC]
#check (AlgebraicGeometry.BivariantClass.existsUnique_of_envelope :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' X'' Y'' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [LocallyOfFiniteType X''.hom] [LocallyOfFiniteType Y''.hom]
    (f : X ⟶ Y) (g : Y' ⟶ Y) [IsEnvelope g.left]
    (h : X' ⟶ X) (f' : X' ⟶ Y')
    (outer : IsPullback h.left f'.left f.left g.left)
    (a b : X'' ⟶ X') (f'' : X'' ⟶ Y'') (q₁ q₂ : Y'' ⟶ Y')
    [LocallyOfFiniteType q₁.left] [LocallyOfFiniteType q₂.left]
    (firstRestriction : IsPullback a.left f''.left f'.left q₁.left)
    (secondRestriction : IsPullback b.left f''.left f'.left q₂.left)
    (sourceRelation : IsPullback a.left b.left h.left h.left)
    (targetRelation : IsPullback q₁.left q₂.left g.left g.left)
    (p : ℤ) (c' : BivariantClass δ f' p)
    (compatible :
      restrict δ a f'' q₁ firstRestriction p c' =
        restrict δ b f'' q₂ secondRestriction p c'),
    ∃! c : BivariantClass δ f p, restrict δ h f' g outer p c = c')

end AlgebraicGeometry.BivariantClass
