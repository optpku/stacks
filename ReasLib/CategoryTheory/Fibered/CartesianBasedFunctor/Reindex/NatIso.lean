/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex.MapIso.Naturality

/-!
# Bundled cartesian-functor reindexing comparison

This module packages the objectwise reindexing comparisons as natural isomorphisms between the
source and target fiber functors.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

universe uS₁ vS₁ uS₂ vS₂

namespace CartesianBasedFunctor

variable {S₁ : Type uS₁} {S₂ : Type uS₂} [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

/-- The comparisons `f⁎[χ₂] (F x) ≅ F (f⁎[χ₁] x)` bundled as the natural isomorphism
`F_U ⋙ f⁎[χ₂] ≅ f⁎[χ₁] ⋙ F_V`. -/
noncomputable def Reindex.natIso
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) :
    F.fiberFunctor U ⋙ f⁎[χ₂] ≅ f⁎[χ₁] ⋙ F.fiberFunctor V :=
  NatIso.ofComponents (Reindex.mapIso F χ₁ χ₂ f)
    (fun α ↦ Reindex.mapIso.hom.naturality F χ₁ χ₂ f α)

/-- The forward component of the bundled reindexing comparison is the objectwise comparison
`Reindex.mapIso`. -/
@[simp]
theorem Reindex.natIso.hom.app
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    (Reindex.natIso F χ₁ χ₂ f).hom.app x =
      (Reindex.mapIso F χ₁ χ₂ f x).hom := sorry

/-- The inverse component of the bundled reindexing comparison is the inverse objectwise
comparison. -/
@[simp]
theorem Reindex.natIso.inv.app
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    (Reindex.natIso F χ₁ χ₂ f).inv.app x =
      (Reindex.mapIso F χ₁ χ₂ f x).inv := sorry

end CartesianBasedFunctor

end CategoryTheory
