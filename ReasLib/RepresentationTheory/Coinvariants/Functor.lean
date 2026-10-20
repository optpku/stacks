/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.RepresentationTheory.Coinvariants

/-!
# The coinvariants functor on monoid-algebra modules
-/

@[expose] public section

open CategoryTheory
open scoped MonoidAlgebra

noncomputable section

universe u v w

namespace MonoidAlgebra.Coinvariants

variable (Λ : Type u) (G : Type v) [Ring Λ] [Monoid G]

/-- A monoid-algebra module morphism induces a coefficient-linear map on coinvariants,
with coefficient actions restricted along the coefficient inclusion. -/
def map {M N : ModuleCat.{w} (Λ[G])} (f : M ⟶ N) :
    Coinvariants Λ G ((ModuleCat.restrictScalars (singleOneRingHom : Λ →+* Λ[G])).obj M) →ₗ[Λ]
      Coinvariants Λ G ((ModuleCat.restrictScalars (singleOneRingHom : Λ →+* Λ[G])).obj N) :=
  lift Λ G _
    ((mk Λ G _).comp
      ((ModuleCat.restrictScalars (singleOneRingHom : Λ →+* Λ[G])).map f).hom)
    fun g x ↦ by
      change mk Λ G ((ModuleCat.restrictScalars (singleOneRingHom : Λ →+* Λ[G])).obj N)
          (f.hom ((single g (1 : Λ) : Λ[G]) • x)) =
        mk Λ G ((ModuleCat.restrictScalars (singleOneRingHom : Λ →+* Λ[G])).obj N) (f.hom x)
      erw [f.hom.map_smul, mk_smul]

/-- The functor taking monoid-algebra modules to their coefficient-module coinvariants. -/
@[reducible] def functor : ModuleCat.{w} (Λ[G]) ⥤ ModuleCat.{w} Λ where
  obj M := ModuleCat.of Λ
    (Coinvariants Λ G ((ModuleCat.restrictScalars (singleOneRingHom : Λ →+* Λ[G])).obj M))
  map f := ModuleCat.ofHom (map Λ G f)
  map_id M := by
    apply ModuleCat.hom_ext
    apply hom_ext Λ G _
    ext x
    simp [map, lift_mk]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply hom_ext Λ G _
    ext x
    simp [map, lift_mk]

/-- The functorial map sends a representative to the class of its image. -/
@[simp] theorem functor_map_mk {M N : ModuleCat.{w} (Λ[G])} (f : M ⟶ N)
    (x : (ModuleCat.restrictScalars (singleOneRingHom : Λ →+* Λ[G])).obj M) :
    (functor Λ G).map f (mk Λ G _ x) =
      mk Λ G ((ModuleCat.restrictScalars (singleOneRingHom : Λ →+* Λ[G])).obj N) (f x) := by
  change map Λ G f (mk Λ G _ x) = _
  simp only [map, lift_mk, LinearMap.comp_apply]
  rfl

/-- Taking coinvariants is additive on monoid-algebra module morphisms. -/
instance instAdditiveFunctor : (functor Λ G : ModuleCat.{w} (Λ[G]) ⥤ ModuleCat.{w} Λ).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply hom_ext Λ G _
    ext x
    change (functor Λ G).map (f + g) (mk Λ G _ x) =
      (functor Λ G).map f (mk Λ G _ x) + (functor Λ G).map g (mk Λ G _ x)
    rw [functor_map_mk, functor_map_mk, functor_map_mk]
    exact (mk Λ G ((ModuleCat.restrictScalars
      (singleOneRingHom : Λ →+* Λ[G])).obj N)).map_add (f x) (g x)

end MonoidAlgebra.Coinvariants
