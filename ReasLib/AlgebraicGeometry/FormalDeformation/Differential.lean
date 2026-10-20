/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Functor.IsomorphismClasses

/-!
# Differential of a based functor
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor
open scoped Bicategory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
namespace CategoryTheory.BasedFunctor

/-- The differential is the map on isomorphism classes induced by restricting a based functor to
the fibre over the dual numbers. -/
def differential (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    isomorphismClasses.obj (Cat.of (p.Fiber (dualNumber Λ k))) →
      isomorphismClasses.obj (Cat.of (q.Fiber (dualNumber Λ k))) :=
  (φ.fiberFunctor (dualNumber Λ k)).isoClassesMap

variable [IsPredeformationCategory p] [IsPredeformationCategory q]

/-- The differential sends the isomorphism class of a fibre object to the class of its image. -/
theorem differential_mk (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (dualNumber Λ k)) :
    differential φ (tangentSpace.mk p x) =
      tangentSpace.mk q ((φ.fiberFunctor (dualNumber Λ k)).obj x) := sorry

/-- The differential of the identity morphism is the identity map on isomorphism classes. -/
theorem differential_id :
    differential (𝟙 (BasedCategory.ofFunctor p)) = fun x ↦ x := sorry

/-- The differential of a composite morphism is the composite of the differentials. -/
theorem differential_comp {H : Type v} [Category.{w} H] {r : H ⥤ ArtinianLocalAlgCat Λ k}
    [IsPredeformationCategory r]
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (ψ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor r) :
    differential (φ ⋙ ψ) = differential ψ ∘ differential φ := sorry

variable [HasSchlessingerH2 (fiberIsoClassFunctor p)]
  [HasSchlessingerH2 (fiberIsoClassFunctor q)]

/-- The differential of a morphism of predeformation categories is linear when both
associated isomorphism-class functors satisfy Schlessinger's condition (H2). -/
theorem isLinearMap_differential (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    (IsLinearMap k :
      ((fiberIsoClassFunctor p).obj (dualNumber Λ k) →
        (fiberIsoClassFunctor q).obj (dualNumber Λ k)) → Prop) (differential φ) := sorry

/-- The differential of a morphism of predeformation categories as a bundled linear map,
when both associated isomorphism-class functors satisfy Schlessinger's condition (H2). -/
noncomputable def differentialLinearMap
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) →ₗ[k]
      (fiberIsoClassFunctor q).obj (dualNumber Λ k) :=
  IsLinearMap.mk' (differential φ) (isLinearMap_differential φ)

/-- The bundled differential evaluates to the canonical map on tangent spaces. -/
theorem differentialLinearMap_apply (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : (fiberIsoClassFunctor p).obj (dualNumber Λ k)) :
    differentialLinearMap φ x = differential φ x := sorry

end CategoryTheory.BasedFunctor
