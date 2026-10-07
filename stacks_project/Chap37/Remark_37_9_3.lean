module

import StacksCheckRecall
import stacks_project.Chap37.Lemma_37_9_2

open AlgebraicGeometry CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

universe u

variable {X X' Y Y' : Scheme.{u}}

/- Remark 37.9.3: `IsPerturbation S i j a a' sqA θ b'` is the Lean rendering of
`b' = θ · a'`; its characterization states that the structure-sheaf maps differ by the
derivation associated to `θ` in Equation 37.9.1.1. -/
@[stacks 0CK1] #check
  (AlgebraicGeometry.Scheme.Hom.Deformation.isPerturbation_iff :
    ∀ (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
      (a : X ⟶ Y) (a' : X' ⟶ Y') [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
      [IsFirstOrderThickening i] [IsFirstOrderThickening j]
      [i.IsOver S] [j.IsOver S] [a.IsOver S] [a'.IsOver S]
      (sqA : CommSq a i j a')
      (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
        Scheme.Hom.conormalSheaf i)
      (b' : X' ⟶ Y'),
      AlgebraicGeometry.Scheme.Hom.Deformation.IsPerturbation
          S i j a a' sqA θ b' ↔
        b' ≫ (Y' ↘ S) = X' ↘ S ∧
          ∃ sqB : CommSq a i j b',
            AlgebraicGeometry.Scheme.Hom.Conormal.map sqA =
              AlgebraicGeometry.Scheme.Hom.Conormal.map sqB ∧
              ∀ (U : (Opens Y)ᵒᵖ)
                (x : (IsFirstOrderThickening.presentationSheaf j).obj.obj U),
                (AlgebraicGeometry.Scheme.Hom.Deformation.presentationDifference
                  sqB sqA).hom.app U x =
                  (SquareZeroExtension.conormalInclusion
                    (IsFirstOrderThickening.presentationProjection i)
                    (IsFirstOrderThickening.presentationKernel_isSquareZero i)).hom.app
                      ((Opens.map a.base).op.obj U)
                      ((d[(Y ↘ S).toShHom].postcomp
                        (((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv _ _) θ).val).d
                          ((IsFirstOrderThickening.presentationProjection j).hom.app U x)))
