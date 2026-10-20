/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap77.«77_7_1_1_BaseChange»

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.IsomorphismFunctor

/-!
# The isomorphism functor of a module morphism on an algebraic space

This module defines the subterminal functor on schemes over an algebraic space `B` that records
the base changes on which a morphism of quasi-coherent modules is an isomorphism.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}
variable {T : Over S} (a : ofOver T ⟶ B)

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver B : Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.mk a : SchemeOver B)

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.mk_left a : (SchemeOver.mk a).left = T)

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.mk_hom a : (SchemeOver.mk a).hom = a)

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
variable (u : ℱ ⟶ 𝒢) (T : SchemeOver B)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_isIso f :
  ∀ {T T' : SchemeOver B} (φ : T' ⟶ T) (u : ℱ ⟶ 𝒢),
    IsIso (baseChangeMap f T.hom u) → IsIso (baseChangeMap f T'.hom u))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismSubfunctor f u :
  CategoryTheory.Subfunctor ((Functor.const (SchemeOver B)ᵒᵖ).obj (PUnit : Type u)))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_isomorphismSubfunctor f u T :
  PUnit.unit ∈ (isomorphismSubfunctor f u).obj (op T) ↔ IsIso (baseChangeMap f T.hom u))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismFunctor f u :
  (SchemeOver B)ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismFunctorObjSubsingleton f u T :
  Subsingleton ((isomorphismFunctor f u).obj (op T)))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismFunctor_obj_nonempty_iff f u T :
  Nonempty ((isomorphismFunctor f u).obj (op T)) ↔ IsIso (baseChangeMap f T.hom u))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismFunctor_obj_isEmpty_iff f u T :
  IsEmpty ((isomorphismFunctor f u).obj (op T)) ↔ ¬ IsIso (baseChangeMap f T.hom u))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismFunctor_obj_nonempty_iff_mk f :
  ∀ {T : Over S} (a : ofOver T ⟶ B) (u : ℱ ⟶ 𝒢),
    Nonempty ((isomorphismFunctor f u).obj (op (SchemeOver.mk a))) ↔
      IsIso (baseChangeMap f a u))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismFunctor_obj_isEmpty_iff_mk f :
  ∀ {T : Over S} (a : ofOver T ⟶ B) (u : ℱ ⟶ 𝒢),
    IsEmpty ((isomorphismFunctor f u).obj (op (SchemeOver.mk a))) ↔
      ¬ IsIso (baseChangeMap f a u))

end AlgebraicGeometry.AlgebraicSpace.Modules
