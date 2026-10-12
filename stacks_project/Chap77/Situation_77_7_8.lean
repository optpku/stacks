/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap77.«77_7_8_1_Flattening»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent] (T : SchemeOver Y)

/- Situation 77.7.8: the base changes of `ℱ` that are flat over a scheme `T` over `Y`
define a subterminal contravariant functor on schemes over `Y`. -/
@[stacks 0CWX] #check
  (Modules.Flattening.functor f ℱ : (SchemeOver Y)ᵒᵖ ⥤ Type u)

#check
  (Modules.baseChangeSpace f T.hom : AlgebraicSpace S)

#check
  (Modules.baseChangeProj f T.hom : Modules.baseChangeSpace f T.hom ⟶ X)

#check
  (Modules.Flattening.baseChange f ℱ T : (Modules.baseChangeSpace f T.hom).Modules)

#check
  (Modules.Flattening.isFlat f ℱ T : Prop)

#check
  (Modules.Flattening.functor_obj_nonempty_iff f ℱ T :
    Nonempty ((Modules.Flattening.functor f ℱ).obj (op T)) ↔
      Modules.Flattening.isFlat f ℱ T)

#check
  (Modules.Flattening.functor_obj_isEmpty_iff f ℱ T :
    IsEmpty ((Modules.Flattening.functor f ℱ).obj (op T)) ↔
      ¬ Modules.Flattening.isFlat f ℱ T)

#check
  (Modules.Flattening.functorObjSubsingleton f ℱ T :
    Subsingleton ((Modules.Flattening.functor f ℱ).obj (op T)))
