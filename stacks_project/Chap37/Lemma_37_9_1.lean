/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Difference
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace Deformation

variable {S X X' Y Y' : Scheme.{u}}

/- Lemma 37.9.1: two morphisms between first-order thickenings over `S` with the same
restriction and the same conormal map differ by an `O_S`-derivation
`O_Y ⟶ a_* C_{X/X'}`; inclusion of its values into `a_* O_{X'}` recovers the difference
of the two ambient structure-sheaf maps. -/
@[stacks 04FG] #check
  (AlgebraicGeometry.Scheme.Hom.Deformation.exists_differenceDerivation :
    ∀ (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
      (a' b' : X' ⟶ Y') [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
      [IsFirstOrderThickening i] [IsFirstOrderThickening j]
      [i.IsOver S] [j.IsOver S] [a.IsOver S] [a'.IsOver S] [b'.IsOver S]
      (sqA : CommSq a i j a') (sqB : CommSq a i j b'),
      Conormal.map sqA = Conormal.map sqB →
        ∃ D : RingedSpace.Hom.derivations (Y ↘ S).toShHom
            ((Scheme.Modules.pushforward a).obj (Scheme.Hom.conormalSheaf i)),
          ∀ (U : (Opens Y)ᵒᵖ)
            (x : (IsFirstOrderThickening.presentationSheaf j).obj.obj U),
            (presentationDifference sqA sqB).hom.app U x =
              (SquareZeroExtension.conormalInclusion
                (IsFirstOrderThickening.presentationProjection i)
                (IsFirstOrderThickening.presentationKernel_isSquareZero i)).hom.app
                  ((Opens.map a.base).op.obj U)
                  (D.d ((IsFirstOrderThickening.presentationProjection j).hom.app U x)))

end Deformation
end Hom
end Scheme
end AlgebraicGeometry
