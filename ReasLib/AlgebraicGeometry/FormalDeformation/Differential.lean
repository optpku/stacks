/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Functor.IsomorphismClasses

/-!
# Differential of a morphism of predeformation categories
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

/-- The differential is the map on isomorphism classes induced by restricting a based functor to
the fibre over the dual numbers. -/
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
