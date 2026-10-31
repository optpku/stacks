/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap42.Definition_42_59_4
public import stacks_project.Chap42.Lemma_42_54_5
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Fundamental
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass


/- Lemma 42.59.8: under preservation of pointwise generic-dimension differences and the
generic Cohen–Macaulay condition, the lci Gysin action satisfies `f^![Y'] = [X']`. -/
@[stacks 0FF7] #check
  (AlgebraicGeometry.BivariantClass.gysin_cap_fundamentalClass :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
    IsPullback i.left f'.left f.left g.left →
    HasGysinMap f →
    (∀ x : X.left, ∃ n, Scheme.Hom.IsGenericDimensionIndex X.hom δ x n) →
    ∀ (hX' : ∀ x' : X'.left, ∃ n, Scheme.Hom.IsGenericDimensionIndex X'.hom δ x' n),
    (∀ y : Y.left, ∃ n, Scheme.Hom.IsGenericDimensionIndex Y.hom δ y n) →
    ∀ (hY' : ∀ y' : Y'.left, ∃ n, Scheme.Hom.IsGenericDimensionIndex Y'.hom δ y' n),
    (∀ (x' : X'.left) (nX' nY' nX nY : ℤ),
      Scheme.Hom.IsGenericDimensionIndex X'.hom δ x' nX' →
      Scheme.Hom.IsGenericDimensionIndex Y'.hom δ (f'.left x') nY' →
      Scheme.Hom.IsGenericDimensionIndex X.hom δ (i.left x') nX →
      Scheme.Hom.IsGenericDimensionIndex Y.hom δ (g.left (f'.left x')) nY →
      nX' - nY' = nX - nY) →
    (∀ ξ : genericPoints X'.left,
      CohenMacaulayRing (Presheaf.stalk Y'.left.presheaf (f'.left ξ.1) : CommRingCat)) →
    Gysin.cap δ f i f' g
        (Scheme.Hom.GenericDimensionStratification.ofPointwise X'.hom δ hX')
        (Scheme.Hom.GenericDimensionStratification.ofPointwise Y'.hom δ hY')
        (ChowGroup.Codimension.fundamentalClass
          (Scheme.Hom.GenericDimensionStratification.ofPointwise Y'.hom δ hY')) =
      Part.some (ChowGroup.Codimension.fundamentalClass
        (Scheme.Hom.GenericDimensionStratification.ofPointwise X'.hom δ hX')))

end AlgebraicGeometry.BivariantClass
