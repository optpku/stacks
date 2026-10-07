module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Functor.IsomorphismClasses
public import stacks_project.Chap90.Definition_90_12_1_TangentSpace

/-!
# Differential of a morphism of predeformation categories

The differential of a morphism of predeformation categories is the map of tangent
spaces obtained by evaluating the associated morphism of isomorphism-class functors at
`DualNumber k`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor
open scoped Bicategory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
variable [IsPredeformationCategory p] [IsPredeformationCategory q]

namespace CategoryTheory.BasedFunctor

/-- Definition 90.12.3: let `φ : ℱ ⟶ 𝒢` be a morphism of predeformation categories. The
differential `dφ` of `φ` is the map obtained by evaluating the morphism of associated
isomorphism-class functors `φ̄ : ℱ̄ ⟶ 𝒢̄` at `A = DualNumber k`. Equivalently, it is the
map on isomorphism classes of the fibre categories `ℱ(DualNumber k) ⟶ 𝒢(DualNumber k)`. -/
@[stacks 06II]
def differential (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    Functor.tangentSpace p → Functor.tangentSpace q :=
  (φ.fiberFunctor (dualNumber Λ k)).isoClassesMap

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

end CategoryTheory.BasedFunctor
