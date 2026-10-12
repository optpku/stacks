/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Pullback
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Pullback.Cone
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory.Functor.IsFibered.InGroupoids.Pullback

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {E : Type u₂} [Category.{v₂} E]
variable (p : E ⥤ C) [Functor.IsFibered.InGroupoids p]
variable {x y z : E} (phi : x ⟶ y) (psi : z ⟶ y)
variable [HasPullback (p.map phi) (p.map psi)]

/- Lemma 4.35.15 (1): pullbacks in the base lift to pullbacks in a category fibred in
groupoids. -/
@[stacks 06N6 "(1)"]
#check (hasPullback p phi psi : HasPullback phi psi)

/- Lemma 4.35.15 (2): the image of the lifted pullback apex is the chosen pullback apex in the
base category. -/
@[stacks 06N6 "(2)"]
#check (Functor.IsStronglyCartesian.Pullback.cone.obj_pt p phi psi :
  p.obj (Functor.IsStronglyCartesian.Pullback.cone p phi psi).pt =
    pullback (p.map phi) (p.map psi))

/- Lemma 4.35.15 (3): the projection of a groupoid-fibred category preserves the lifted
pullback in the base. -/
@[stacks 06N6 "(3) pullback preservation in the base"]
#check (inferInstance : PreservesLimitsOfShape WalkingCospan p)

end CategoryTheory.Functor.IsFibered.InGroupoids.Pullback
