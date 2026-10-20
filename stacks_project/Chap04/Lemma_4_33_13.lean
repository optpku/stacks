/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Pullback
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {E : Type u₂} [Category.{v₂} E]
variable (p : E ⥤ C) {x y z : E} (phi : x ⟶ y) (psi : z ⟶ y)
variable [p.IsFibered] [HasPullback (p.map phi) (p.map psi)]
variable [p.IsStronglyCartesian (p.map phi) phi]

/- Lemma 4.33.13 (1): the canonical lifted pullback square exists in the total category. -/
@[stacks 06N5 "canonical lifted pullback exists"]
#check (Functor.IsStronglyCartesian.Pullback.cone.isLimit p phi psi :
  IsLimit (Functor.IsStronglyCartesian.Pullback.cone p phi psi))

/- Lemma 4.33.13 (2): the image of the lifted pullback apex is the chosen pullback apex in the
base category. -/
@[stacks 06N5 "image of lifted pullback apex"]
#check (Functor.IsStronglyCartesian.Pullback.cone.obj_pt p phi psi :
  p.obj (Functor.IsStronglyCartesian.Pullback.cone p phi psi).pt =
    pullback (p.map phi) (p.map psi))

/- Lemma 4.33.13 (3): the canonical second projection of the lifted pullback is strongly
cartesian. -/
@[stacks 06N5 "strongly cartesian lifted second projection"]
#check (inferInstance :
  p.IsStronglyCartesian (pullback.snd (p.map phi) (p.map psi))
    (Functor.IsPreFibered.pullbackMap (p := p) rfl
      (pullback.snd (p.map phi) (p.map psi))))

end CategoryTheory
