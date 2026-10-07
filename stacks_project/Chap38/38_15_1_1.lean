module

import StacksCheckRecall
import stacks_project.Chap38.Situation_38_15_1
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
import ReasLib.AlgebraicGeometry.Scheme.Pullback.Square
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

section

variable {S X : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f]
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S)
variable {T : Scheme.{u}} (g : T ⟶ S) (t' t : T)
variable (h_specializes : t' ⤳ t) (map_specialPoint : g t = s)
variable (ξ : (pullback f g : Scheme)) (map_point : pullback.snd f g ξ = t')

/- 38.15.1.1: the configuration consists of `ξ` mapping to `t'`, a specialization
`t' ⤳ t` with `g t = s`, and the canonical pullback square `X ×_S T ⟶ X` over `T ⟶ S`. -/
@[stacks 05IX] #check
  (AlgebraicGeometry.Scheme.Pullback.isPullback f g :
    CategoryTheory.IsPullback (pullback.fst f g) (pullback.snd f g) f g)

#check (h_specializes : t' ⤳ t)
#check (map_specialPoint : g t = s)
#check (map_point : pullback.snd f g ξ = t')
#check Scheme.Pullback.Triplet.ofPoint ξ

end
