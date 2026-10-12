/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import ReasLib.CategoryTheory.Sites.HigherDirectImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasInjectiveResolutions
  (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable (p : {n : ℕ // 1 ≤ n})

/- Definition 59.35.4: for a morphism `f : X ⟶ Y` of schemes, the positive-degree
right derived functors of the étale direct image are called higher direct images. -/
@[stacks 04I2] #check
  (CategoryTheory.Sheaf.higherDirectImageFunctor
    (Scheme.smallEtalePullback f) p.1 :
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})

end
