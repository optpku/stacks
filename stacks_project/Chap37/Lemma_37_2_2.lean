/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.SquareZeroExtension
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.2.2 (1): a locally surjective square-zero extension of `X.sheaf` with
quasi-coherent kernel explicitly defines a first-order thickening over `S`. -/
@[stacks 05YV] #check
  (@AlgebraicGeometry.Scheme.SquareZeroExtension.inclusion_isFirstOrderThickening :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} [X.Over S]
      (A : TopCat.Sheaf CommRingCat.{u} X.toTopCat) (π : A ⟶ X.sheaf)
      [CategoryTheory.Sheaf.IsLocallySurjective π]
      (hπ : SheafOfModules.RingedSite.KernelIdeal.IsSquareZero π)
      [(AlgebraicGeometry.Scheme.SquareZeroExtension.kernelModule A π hπ).IsQuasicoherent]
      (α : AlgebraicGeometry.Scheme.SquareZeroExtension.baseSheaf S X ⟶ A)
      (hα : α ≫ π =
        AlgebraicGeometry.Scheme.SquareZeroExtension.baseProjection S X),
      AlgebraicGeometry.IsFirstOrderThickening
        (AlgebraicGeometry.Scheme.SquareZeroExtension.inclusion A π hπ α hα).left)

/- Lemma 37.2.2 (2): every first-order thickening over `S` is recovered from its inverse-image
structure sheaf by the canonical comparison over `S`. -/
@[stacks 05YV] #check
  (@AlgebraicGeometry.IsFirstOrderThickening.reconstruction :
    ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (i : X ⟶ X')
      [AlgebraicGeometry.IsFirstOrderThickening i] (S : AlgebraicGeometry.Scheme.{u})
      [X.Over S] [X'.Over S] [i.IsOver S],
      AlgebraicGeometry.IsFirstOrderThickening.reconstructedInclusion i S ≫
          AlgebraicGeometry.IsFirstOrderThickening.reconstructionOverHom i S =
        i.asOver S)

/- The reconstruction comparison is an isomorphism over `S`. -/
#check
  (@AlgebraicGeometry.IsFirstOrderThickening.reconstructionOverHom_isIso :
    ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (i : X ⟶ X')
      [AlgebraicGeometry.IsFirstOrderThickening i] (S : AlgebraicGeometry.Scheme.{u})
      [X.Over S] [X'.Over S] [i.IsOver S],
      IsIso (AlgebraicGeometry.IsFirstOrderThickening.reconstructionOverHom i S))
