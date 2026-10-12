/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.SquareZeroExtension

@[expose] public section

open CategoryTheory

universe u

#check
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

#check
  (@AlgebraicGeometry.IsFirstOrderThickening.reconstructionOverHom_isIso :
    ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (i : X ⟶ X')
      [AlgebraicGeometry.IsFirstOrderThickening i] (S : AlgebraicGeometry.Scheme.{u})
      [X.Over S] [X'.Over S] [i.IsOver S],
      IsIso (AlgebraicGeometry.IsFirstOrderThickening.reconstructionOverHom i S))

#check
  (@AlgebraicGeometry.IsFirstOrderThickening.reconstruction :
    ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (i : X ⟶ X')
      [AlgebraicGeometry.IsFirstOrderThickening i] (S : AlgebraicGeometry.Scheme.{u})
      [X.Over S] [X'.Over S] [i.IsOver S],
      AlgebraicGeometry.IsFirstOrderThickening.reconstructedInclusion i S ≫
          AlgebraicGeometry.IsFirstOrderThickening.reconstructionOverHom i S =
        i.asOver S)
