/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.RegularImmersion
public import stacks_project.Chap42.Lemma_42_55_3_NormalClass
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.BivariantClass
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

noncomputable section

universe u

/- Lemma 42.59.1: regular immersions have regular composite, and the completed Gysin
class of the composite is the convolution of their completed Gysin classes. -/
@[stacks 0FF0] #check (AlgebraicGeometry.BivariantClass.gysin_comp :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsRegularImmersion i.left] [IsRegularImmersion j.left]
    (ei : Scheme.Modules.dual (Scheme.Hom.normalSheaf i.left) ≅
      Scheme.Hom.conormalSheaf i.left)
    (ej : Scheme.Modules.dual (Scheme.Hom.normalSheaf j.left) ≅
      Scheme.Hom.conormalSheaf j.left)
    (eij : Scheme.Modules.dual (Scheme.Hom.normalSheaf (i.left ≫ j.left)) ≅
      Scheme.Hom.conormalSheaf (i.left ≫ j.left))
    (Di : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ Y.hom)
      i.left.liftCoborder
      (factorization_over X.hom Y.hom i.left i.w
        i.left.liftCoborder i.left.coborderRange.ι i.left.liftCoborder_ι)
      (normalSheafBundle i.left ei).toCoborder)
    (Dj : ClosedDeformation Y.hom (j.left.coborderRange.ι ≫ Z.hom)
      j.left.liftCoborder
      (factorization_over Y.hom Z.hom j.left j.w
        j.left.liftCoborder j.left.coborderRange.ι j.left.liftCoborder_ι)
      (normalSheafBundle j.left ej).toCoborder)
    (Dij : ClosedDeformation X.hom
      ((i.left ≫ j.left).coborderRange.ι ≫ Z.hom)
      (i.left ≫ j.left).liftCoborder
      (factorization_over X.hom Z.hom (i.left ≫ j.left) (i ≫ j).w
        (i.left ≫ j.left).liftCoborder (i.left ≫ j.left).coborderRange.ι
        (i.left ≫ j.left).liftCoborder_ι)
      (normalSheafBundle (i.left ≫ j.left) eij).toCoborder)
    (n : ℕ),
    @Finset.sum
        {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}
        (BivariantClass δ (i ≫ j) (n : ℤ))
        (pointwiseAddCommGroup δ (i ≫ j) (n : ℤ)).toAddCommMonoid
        Finset.univ
        (fun ij ↦
          Nonnegative.castGrading δ (Nonnegative.antidiagonalDegree n ij)
            (comp δ i j
              (overHom_eq_over i ▸ coborder_factorization i ▸
                Nonnegative.castGrading δ (gysin_open_degree ij.1.1)
                  (gysinImmersion δ i ei Di ij.1.1))
              (overHom_eq_over j ▸ coborder_factorization j ▸
                Nonnegative.castGrading δ (gysin_open_degree ij.1.2)
                  (gysinImmersion δ j ej Dj ij.1.2)))) =
      overHom_eq_over (i ≫ j) ▸ coborder_factorization (i ≫ j)
        (immersion := inferInstanceAs (IsImmersion (i.left ≫ j.left))) ▸
        Nonnegative.castGrading δ (gysin_open_degree n)
          (gysinImmersion δ (i ≫ j)
            (regular := inferInstanceAs (IsRegularImmersion (i.left ≫ j.left))) eij Dij n))

/- The composite of two regular immersions is a regular immersion. -/
#check (@AlgebraicGeometry.isRegularImmersion_comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [AlgebraicGeometry.IsRegularImmersion i] [AlgebraicGeometry.IsRegularImmersion j],
    AlgebraicGeometry.IsRegularImmersion (i ≫ j))
