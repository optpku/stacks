module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Perturbation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

variable {X X' Y Y' : Scheme.{u}}

/- Lemma 37.9.2: an `𝒪_X`-linear map from the pullback of `Ω_{Y/S}` to the conormal
sheaf of `X ⟶ X'` uniquely determines a perturbation of the ambient morphism. -/
@[stacks 02H5] #check
  (AlgebraicGeometry.Scheme.Hom.Deformation.existsUnique_perturbation :
    ∀ (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
      (a : X ⟶ Y) (a' : X' ⟶ Y') [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
      [IsFirstOrderThickening i] [IsFirstOrderThickening j]
      [i.IsOver S] [j.IsOver S] [a.IsOver S] [a'.IsOver S]
      (sqA : CommSq a i j a')
      (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
        Scheme.Hom.conormalSheaf i),
      ∃! b' : X' ⟶ Y',
        AlgebraicGeometry.Scheme.Hom.Deformation.IsPerturbation
          S i j a a' sqA θ b')
