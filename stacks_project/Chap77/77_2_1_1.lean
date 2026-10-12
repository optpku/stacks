/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import stacks_project.Chap65.Definition_65_6_3_Hom
import stacks_project.Chap65.Lemma_65_6_2_OfOver
import stacks_project.Chap65.Lemma_65_7_3_Pullback
import stacks_project.Chap66.Definition_66_4_1_Points
import stacks_project.Chap66.Definition_66_29_1_RingedSite
import stacks_project.Chap66.Lemma_66_4_2_Comparison
import stacks_project.Chap66.Lemma_66_29_2_Pullback
import stacks_project.Chap67.Definition_67_40_1_FiniteType
import stacks_project.Chap68.Lemma_68_17_4_Relative

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

section

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f] [Decent f]
variable (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
variable {T : Over S} (g : ofOver T ⟶ Y) (t' t : T.left)
variable (h_specializes : t' ⤳ t)
variable (map_specialPoint : Points.map g (ofOver.pointsEquiv T t) = y)
variable (ξ : Points (pullback f g))
variable (map_point : Points.map (pullback.snd f g) ξ = ofOver.pointsEquiv T t')

/- 77.2.1.1: the configuration consists of `ξ` mapping to `t'`, a specialization
`t' ⤳ t` with image `y`, and the cartesian square `pullback f g ⟶ X` over
`ofOver T ⟶ Y`. -/
@[stacks 0CV7] #check
  (IsPullback.of_hasPullback f g :
    IsPullback (pullback.fst f g) (pullback.snd f g) f g)

#check (h_specializes : t' ⤳ t)
#check (map_specialPoint : Points.map g (ofOver.pointsEquiv T t) = y)
#check (map_point : Points.map (pullback.snd f g) ξ = ofOver.pointsEquiv T t')
#check ((Modules.pullback (pullback.fst f g)).obj F : (pullback f g).Modules)

end
