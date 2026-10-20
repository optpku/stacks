/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Flattening

/-!
# The flattening functor on schemes over an algebraic space

Typed checks of the flattening construction and its flatness specifications.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent] (T : SchemeOver Y)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.baseChange f ℱ T :
    (Modules.baseChangeSpace f T.hom).Modules)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.baseChange_eq f ℱ T :
    Modules.Flattening.baseChange f ℱ T = Modules.baseChangeModule f T.hom ℱ)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.isFlat f ℱ T : Prop)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.isFlat_iff f ℱ T :
    Modules.Flattening.isFlat f ℱ T ↔
      Modules.flatOver (Modules.baseChangeModule f T.hom ℱ) (Limits.pullback.snd f T.hom))

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.isFlat_of_hom f ℱ :
    ∀ {T U : SchemeOver Y}, (T ⟶ U) →
      Modules.Flattening.isFlat f ℱ U → Modules.Flattening.isFlat f ℱ T)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.subfunctor f ℱ :
    CategoryTheory.Subfunctor ((Functor.const (SchemeOver Y)ᵒᵖ).obj (PUnit : Type u)))

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.mem_subfunctor f ℱ T :
    PUnit.unit ∈ (Modules.Flattening.subfunctor f ℱ).obj (op T) ↔
      Modules.Flattening.isFlat f ℱ T)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.functor f ℱ :
    (SchemeOver Y)ᵒᵖ ⥤ Type u)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.functorObjSubsingleton f ℱ T :
    Subsingleton ((Modules.Flattening.functor f ℱ).obj (op T)))

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.functor_obj_nonempty_iff f ℱ T :
    Nonempty ((Modules.Flattening.functor f ℱ).obj (op T)) ↔
      Modules.Flattening.isFlat f ℱ T)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.functor_obj_isEmpty_iff f ℱ T :
    IsEmpty ((Modules.Flattening.functor f ℱ).obj (op T)) ↔
      ¬ Modules.Flattening.isFlat f ℱ T)

variable {T' : Over S} (a : ofOver T' ⟶ Y)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.functor_obj_nonempty_iff_mk f ℱ a :
    Nonempty ((Modules.Flattening.functor f ℱ).obj (op (SchemeOver.mk a))) ↔
      Modules.flatOver (Modules.baseChangeModule f a ℱ) (Limits.pullback.snd f a))

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.functor_obj_isEmpty_iff_mk f ℱ a :
    IsEmpty ((Modules.Flattening.functor f ℱ).obj (op (SchemeOver.mk a))) ↔
      ¬ Modules.flatOver (Modules.baseChangeModule f a ℱ) (Limits.pullback.snd f a))
