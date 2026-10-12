/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

/- Remark 59.35.2 (1): the small étale pullback associated to a scheme morphism is
continuous, expressing stability of étale coverings under base change. -/
@[stacks 03PX] #check
  (AlgebraicGeometry.Scheme.smallEtalePullback_isContinuous :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S),
      (Scheme.smallEtalePullback f).IsContinuous S.smallEtaleTopology
        T.smallEtaleTopology)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (F : Sheaf X.smallEtaleTopology (Type v))

/- Remark 59.35.2 (2): the direct image of a sheaf along a scheme morphism is
a sheaf on the target small étale site. -/
@[stacks 03PX] #check
  ((AlgebraicGeometry.Scheme.smallEtaleDirectImage f).obj F :
      Sheaf Y.smallEtaleTopology (Type v))
