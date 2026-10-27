/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme
public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic

/-!
# Target projection of scheme morphism deformations

Forgetting a flat scheme morphism to its target induces a functor on residue
slices that preserves the Artinian local base strictly.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry BasedFunctor

noncomputable section

universe u

namespace FlatSchemeMorphismCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The target pair `(A, Y)` attached to a morphism pair `(A, X ⟶ Y)`. -/
def targetObj (P : FlatSchemeMorphismCat Λ k) : FlatSchemeCat Λ k :=
  FlatSchemeCat.of P.base P.target P.targetOver (targetFlat P)

/-- The target comparison keeps the base map and the stored target scheme map. -/
def targetMap {src tgt : FlatSchemeMorphismCat Λ k} (φ : src ⟶ tgt) :
    targetObj src ⟶ targetObj tgt where
  baseHom := φ.base
  schemeHom := φ.targetMap
  isPullback := φ.isPullback_bot

/-- The functor forgetting a flat scheme morphism to its target scheme. -/
def targetFunctor (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k] :
    FlatSchemeMorphismCat Λ k ⥤ FlatSchemeCat Λ k :=
  let laws : (∀ P : FlatSchemeMorphismCat Λ k, targetMap (𝟙 P) = 𝟙 (targetObj P)) ∧
      (∀ {P Q R : FlatSchemeMorphismCat Λ k} (φ : P ⟶ Q) (ψ : Q ⟶ R),
        targetMap (φ ≫ ψ) = targetMap φ ≫ targetMap ψ) := sorry
  { obj := targetObj
    map := targetMap
    map_id := laws.1
    map_comp := laws.2 }

variable (Λ k)

/-- The functor on deformation slices sends a deformation of a scheme morphism to its target. -/
def targetDeformationFunctor (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    deformation Λ k X Y f hX hY hf ⥤ FlatSchemeCat.deformationCategory Λ k Y hY :=
  Over.post (targetFunctor Λ k)

/-- The target deformation functor preserves the Artinian local base strictly. -/
theorem targetDeformationFunctor_comp_forget (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    targetDeformationFunctor Λ k X Y f hX hY hf ⋙
        Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k Y hY)) ⋙
          FlatSchemeCat.forget Λ k =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙
        forget Λ k :=
  sorry

/-- The target deformation functor bundled over the category of Artinian local algebras. -/
def targetBasedFunctor (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙
          forget Λ k) ⥤ᵇ
      BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k Y hY)) ⋙
          FlatSchemeCat.forget Λ k) :=
  BasedFunctor.ofFunctor (targetDeformationFunctor Λ k X Y f hX hY hf)
    (targetDeformationFunctor_comp_forget Λ k X Y f hX hY hf)

end FlatSchemeMorphismCat

end
