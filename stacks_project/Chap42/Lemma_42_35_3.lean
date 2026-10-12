/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Vanishing
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/- Lemma 42.35.3: pointwise vanishing of a bivariant class, vanishing on every
integral fundamental class, and vanishing after a modification of every integral
test scheme are equivalent. -/
@[stacks 02UC] #check
  (AlgebraicGeometry.BivariantClass.vanishingEquivalences :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
      [IsDimensionFunction delta] (X Y : Over S)
      [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) (p : ℤ) (c : BivariantClass delta f p),
      ((∀ {X' Y' : Over S}
          [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
          (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
          [LocallyOfFiniteType g.left]
          (square : IsPullback i.left f'.left f.left g.left) (k : ℤ),
            c.cap i f' g square k = 0) ↔
        ∀ (V : Over Y.left) [LocallyOfFiniteType V.hom] [IsIntegral V.left],
          BivariantClass.capFundamentalClass delta X Y f p V c = 0) ∧
      ((∀ (V : Over Y.left) [LocallyOfFiniteType V.hom] [IsIntegral V.left],
          BivariantClass.capFundamentalClass delta X Y f p V c = 0) ↔
        ∀ (V : Over Y.left) [LocallyOfFiniteType V.hom] [IsIntegral V.left],
          ∃ (V' : Over V.left) (hmod : IsModification V'.hom),
            BivariantClass.capFundamentalClassAfterModification
              delta X Y f p V V' hmod c = 0))

end AlgebraicGeometry
