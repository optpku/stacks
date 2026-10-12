/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsThickening

/- Lemma 37.10.4 (1): under the stated finiteness and cartesian hypotheses for
a commutative diagram of thickenings, `f'` is flat. -/
@[stacks 0CF3]
#check
  (AlgebraicGeometry.IsThickening.flatAmbient :
    {X X' Y Y' S S' : Scheme.{u}} →
    {iX : X ⟶ X'} → {iY : Y ⟶ Y'} → {iS : S ⟶ S'} →
    {f : X ⟶ Y} → {f' : X' ⟶ Y'} →
    {pX : X ⟶ S} → {pX' : X' ⟶ S'} → {pY : Y ⟶ S} → {pY' : Y' ⟶ S'} →
    [IsThickening iX] → [IsThickening iY] → [IsThickening iS] →
    [LocallyOfFiniteType pY'] → [Flat pX'] →
    [LocallyOfFinitePresentation pX'] → [Flat f] →
    CommSq f iX iY f' →
    f ≫ pY = pX → f' ≫ pY' = pX' →
    IsPullback pX iX iS pX' → IsPullback pY iY iS pY' →
    Flat f')

/- Lemma 37.10.4 (2): under the stated finiteness and cartesian hypotheses for
a commutative diagram of thickenings, `pY'` is flat at every point in the image
of `f'`. -/
@[stacks 0CF3]
#check
  (AlgebraicGeometry.IsThickening.flatAtTarget :
    {X X' Y Y' S S' : Scheme.{u}} →
    {iX : X ⟶ X'} → {iY : Y ⟶ Y'} → {iS : S ⟶ S'} →
    {f : X ⟶ Y} → {f' : X' ⟶ Y'} →
    {pX : X ⟶ S} → {pX' : X' ⟶ S'} → {pY : Y ⟶ S} → {pY' : Y' ⟶ S'} →
    [IsThickening iX] → [IsThickening iY] → [IsThickening iS] →
    [LocallyOfFiniteType pY'] → [Flat pX'] →
    [LocallyOfFinitePresentation pX'] → [Flat f] →
    CommSq f iX iY f' →
    f ≫ pY = pX → f' ≫ pY' = pX' →
    IsPullback pX iX iS pX' → IsPullback pY iY iS pY' →
    ∀ y' : Y', y' ∈ Set.range f' → pY'.flatAt y')

/- Lemma 37.10.4 (3): under the stated finiteness and cartesian hypotheses for
a commutative diagram of thickenings, the induced stalk map at every point in
the image of `f'` is essentially of finite presentation. -/
@[stacks 0CF3]
#check
  (AlgebraicGeometry.IsThickening.essFinitePresentationAtTarget :
    {X X' Y Y' S S' : Scheme.{u}} →
    {iX : X ⟶ X'} → {iY : Y ⟶ Y'} → {iS : S ⟶ S'} →
    {f : X ⟶ Y} → {f' : X' ⟶ Y'} →
    {pX : X ⟶ S} → {pX' : X' ⟶ S'} → {pY : Y ⟶ S} → {pY' : Y' ⟶ S'} →
    [IsThickening iX] → [IsThickening iY] → [IsThickening iS] →
    [LocallyOfFiniteType pY'] → [Flat pX'] →
    [LocallyOfFinitePresentation pX'] → [Flat f] →
    CommSq f iX iY f' →
    f ≫ pY = pX → f' ≫ pY' = pX' →
    IsPullback pX iX iS pX' → IsPullback pY iY iS pY' →
    ∀ y' : Y', y' ∈ Set.range f' →
      (pY'.stalkMap y').hom.EssFinitePresentation)

end AlgebraicGeometry.IsThickening
