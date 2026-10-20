/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Intersection

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

#check (AlgebraicGeometry.BivariantClass.instIsClosedImmersionHomMk :
  ∀ {S : Scheme.{u}} {X : Over S} {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i],
    IsClosedImmersion
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left)

#check (AlgebraicGeometry.BivariantClass.intersectionMul :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {W X₂ X₂' X : Over S} [LocallyOfFiniteType W.hom]
    [LocallyOfFiniteType X₂.hom] [LocallyOfFiniteType X₂'.hom]
    [LocallyOfFiniteType X.hom]
    (i₂ : X₂ ⟶ X) (i₂' : X₂' ⟶ X) (j₂ : W ⟶ X₂) (j₂' : W ⟶ X₂')
    (iW : W ⟶ X) [LocallyOfFiniteType i₂'.left]
    (square : IsPullback j₂.left j₂'.left i₂.left i₂'.left)
    (intersection : j₂' ≫ i₂' = iW) {a b : ℤ}
    (c : BivariantClass δ i₂ a) (d : BivariantClass δ i₂' b),
    BivariantClass δ iW (a + b))

#check (AlgebraicGeometry.BivariantClass.intersectionMul_def :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {W X₂ X₂' X : Over S} [LocallyOfFiniteType W.hom]
    [LocallyOfFiniteType X₂.hom] [LocallyOfFiniteType X₂'.hom]
    [LocallyOfFiniteType X.hom]
    (i₂ : X₂ ⟶ X) (i₂' : X₂' ⟶ X) (j₂ : W ⟶ X₂) (j₂' : W ⟶ X₂')
    (iW : W ⟶ X) [LocallyOfFiniteType i₂'.left]
    (square : IsPullback j₂.left j₂'.left i₂.left i₂'.left)
    (intersection : j₂' ≫ i₂' = iW) {a b : ℤ}
    (c : BivariantClass δ i₂ a) (d : BivariantClass δ i₂' b),
    intersectionMul δ i₂ i₂' j₂ j₂' iW square intersection c d =
      intersection ▸ comp δ j₂' i₂' (restrict δ j₂ j₂' i₂' square a c) d)

end AlgebraicGeometry.BivariantClass
