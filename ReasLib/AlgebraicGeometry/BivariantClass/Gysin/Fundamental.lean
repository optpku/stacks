/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Descent
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import ReasLib.RingTheory.CohenMacaulay.Ring

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- For a cartesian square of locally equidimensional schemes over a dimension-function base,
the Gysin action of a local complete intersection morphism admitting an immersion–smooth
factorization sends the full fundamental class of the lower scheme to that of its inverse
image, provided the pointwise generic-dimension differences agree and the lower scheme has
Cohen–Macaulay stalks at the images of generic points of the inverse image. The equality
also asserts that the partial Gysin action is defined. -/
theorem gysin_cap_fundamentalClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (square : IsPullback i.left f'.left f.left g.left)
    (hf : HasGysinMap f)
    (hX : ∀ x : X.left, ∃ n, Scheme.Hom.IsGenericDimensionIndex X.hom δ x n)
    (hX' : ∀ x' : X'.left, ∃ n, Scheme.Hom.IsGenericDimensionIndex X'.hom δ x' n)
    (hY : ∀ y : Y.left, ∃ n, Scheme.Hom.IsGenericDimensionIndex Y.hom δ y n)
    (hY' : ∀ y' : Y'.left, ∃ n, Scheme.Hom.IsGenericDimensionIndex Y'.hom δ y' n)
    (hdim : ∀ (x' : X'.left) (nX' nY' nX nY : ℤ),
      Scheme.Hom.IsGenericDimensionIndex X'.hom δ x' nX' →
      Scheme.Hom.IsGenericDimensionIndex Y'.hom δ (f'.left x') nY' →
      Scheme.Hom.IsGenericDimensionIndex X.hom δ (i.left x') nX →
      Scheme.Hom.IsGenericDimensionIndex Y.hom δ (g.left (f'.left x')) nY →
      nX' - nY' = nX - nY)
    (hCM : ∀ ξ : genericPoints X'.left,
      CohenMacaulayRing (Presheaf.stalk Y'.left.presheaf (f'.left ξ.1) : CommRingCat)) :
    Gysin.cap δ f i f' g
        (Scheme.Hom.GenericDimensionStratification.ofPointwise X'.hom δ hX')
        (Scheme.Hom.GenericDimensionStratification.ofPointwise Y'.hom δ hY')
        (ChowGroup.Codimension.fundamentalClass
          (Scheme.Hom.GenericDimensionStratification.ofPointwise Y'.hom δ hY')) =
      Part.some (ChowGroup.Codimension.fundamentalClass
        (Scheme.Hom.GenericDimensionStratification.ofPointwise X'.hom δ hX')) := sorry


end AlgebraicGeometry.BivariantClass
