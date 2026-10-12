/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Difference.Diagonal
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Deformation

/- Lemma 37.9.8: the derivation measuring the difference between two lifts `a'` and `b'`
is the universal derivation `d[(Y ↘ S).toShHom]` postcomposed with the adjoint of the
induced map from pulled-back relative differentials to the conormal sheaf. -/
@[stacks 04FL] #check
  (AlgebraicGeometry.Scheme.Hom.Deformation.differenceDerivation_eq_postcomp :
    ∀ {S X X' Y : Scheme.{u}} (i : X ⟶ X') (a : X ⟶ Y)
      (a' b' : X' ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S]
      [IsFirstOrderThickening i] [i.IsOver S] [a.IsOver S] [a'.IsOver S] [b'.IsOver S]
      (sqA : CommSq a i (𝟙 Y) a') (sqB : CommSq a i (𝟙 Y) b')
      (D : RingedSpace.Hom.derivations (Y ↘ S).toShHom
        ((Modules.pushforward a).obj (conormalSheaf i)))
      (hD : ∀ (U : (Opens Y)ᵒᵖ)
        (x : (IsFirstOrderThickening.presentationSheaf (𝟙 Y)).obj.obj U),
        (presentationDifference sqA sqB).hom.app U x =
          (SquareZeroExtension.conormalInclusion
            (IsFirstOrderThickening.presentationProjection i)
            (IsFirstOrderThickening.presentationKernel_isSquareZero i)).hom.app
              ((Opens.map a.base).op.obj U)
              (D.d ((IsFirstOrderThickening.presentationProjection (𝟙 Y)).hom.app U x))),
      D = (d[(Y ↘ S).toShHom]).postcomp
        (((Modules.pullbackPushforwardAdjunction a).homEquiv _ _)
          (differenceConormalMap S i a a' b' sqA sqB)).val)

end AlgebraicGeometry.Scheme.Hom.Deformation
