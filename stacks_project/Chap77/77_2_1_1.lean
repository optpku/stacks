/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback.Specialization
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions

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
  (AlgebraicGeometry.AlgebraicSpace.SpecializationDiagram f y : Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.SpecializationDiagram.of f y T g t' t
  h_specializes map_specialPoint ξ map_point :
  AlgebraicGeometry.AlgebraicSpace.SpecializationDiagram f y)
#check ((Modules.pullback (pullback.fst f g)).obj F : (pullback f g).Modules)

end
