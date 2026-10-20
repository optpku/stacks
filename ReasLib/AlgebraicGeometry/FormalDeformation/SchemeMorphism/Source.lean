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
# Source projection of scheme morphism deformations

Forgetting a flat scheme morphism to its source induces a functor on residue
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

/-- The source pair `(A, X)` attached to a morphism pair `(A, X ⟶ Y)`. -/
def sourceObj (P : FlatSchemeMorphismCat Λ k) : FlatSchemeCat Λ k :=
  FlatSchemeCat.of P.base P.source P.sourceOver (sourceFlat P)

/-- The source pair keeps the original Artinian local base. -/
theorem sourceObj_base (P : FlatSchemeMorphismCat Λ k) :
    (sourceObj P).base = P.base :=
  sorry

/-- The source pair has underlying scheme equal to the stored source. -/
theorem sourceObj_scheme (P : FlatSchemeMorphismCat Λ k) :
    (sourceObj P).scheme = P.source :=
  sorry

/-- The source of the residue morphism `(k, X ⟶ Y)` is the residue pair `(k, X)`. -/
theorem sourceObj_ofResidue (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    sourceObj (ofResidue Λ k X Y f hX hY hf) = FlatSchemeCat.ofResidue Λ k X hX :=
  sorry

/-- The source scheme map of a cartesian morphism forms a cartesian square over the base. -/
theorem sourceMap_isPullback {src tgt : FlatSchemeMorphismCat Λ k} (φ : src ⟶ tgt) :
    IsPullback φ.sourceMap tgt.sourceOver src.sourceOver (FlatSchemeCat.specMap φ.base) :=
  sorry

/-- The source comparison morphism retains the base map and reversed source scheme map. -/
def sourceMap {src tgt : FlatSchemeMorphismCat Λ k} (φ : src ⟶ tgt) :
    sourceObj src ⟶ sourceObj tgt where
  baseHom := φ.base
  schemeHom := φ.sourceMap
  isPullback := sourceMap_isPullback φ

/-- Source comparison morphisms preserve the underlying morphism of Artinian local algebras. -/
theorem sourceMap_base {src tgt : FlatSchemeMorphismCat Λ k} (φ : src ⟶ tgt) :
    (sourceMap φ).baseHom = φ.base :=
  sorry

/-- Source comparison morphisms use the stored source scheme morphism. -/
theorem sourceMap_schemeHom {src tgt : FlatSchemeMorphismCat Λ k} (φ : src ⟶ tgt) :
    (sourceMap φ).schemeHom = φ.sourceMap :=
  sorry

/-- Source projection sends an identity morphism to the identity of its source pair. -/
theorem sourceFunctor_map_id (P : FlatSchemeMorphismCat Λ k) :
    sourceMap (𝟙 P) = 𝟙 (sourceObj P) :=
  sorry

/-- Source projection preserves composition of cartesian morphisms. -/
theorem sourceFunctor_map_comp {src mid tgt : FlatSchemeMorphismCat Λ k}
    (φ : src ⟶ mid) (ψ : mid ⟶ tgt) :
    sourceMap (φ ≫ ψ) = sourceMap φ ≫ sourceMap ψ :=
  sorry

variable (Λ k)

/-- The ordinary forgetful functor `(A, X ⟶ Y) ↦ (A, X)` on flat scheme morphisms. -/
def sourceFunctor : FlatSchemeMorphismCat Λ k ⥤ FlatSchemeCat Λ k where
  obj := sourceObj
  map := sourceMap
  map_id := sourceFunctor_map_id
  map_comp := sourceFunctor_map_comp

/-- Objects of the source functor are the source pairs `(A, X)`. -/
theorem sourceFunctor_obj (P : FlatSchemeMorphismCat Λ k) :
    (sourceFunctor Λ k).obj P = sourceObj P :=
  sorry

/-- The source functor lies strictly over the category of Artinian local algebras. -/
theorem sourceFunctor_comp_forget :
    sourceFunctor Λ k ⋙ FlatSchemeCat.forget Λ k = forget Λ k :=
  sorry

/-- The functor on deformation slices sends a deformation of a scheme morphism to its source. -/
def sourceDeformationFunctor (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    deformation Λ k X Y f hX hY hf ⥤ FlatSchemeCat.deformationCategory Λ k X hX :=
  Over.post (sourceFunctor Λ k)

/-- The source deformation functor preserves the Artinian local base strictly. -/
theorem sourceDeformationFunctor_comp_forget (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    sourceDeformationFunctor Λ k X Y f hX hY hf ⋙
        Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)) ⋙
          FlatSchemeCat.forget Λ k =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙
        forget Λ k :=
  sorry

/-- The source deformation functor bundled over the category of Artinian local algebras. -/
def sourceBasedFunctor (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙
          forget Λ k) ⥤ᵇ
      BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)) ⋙
          FlatSchemeCat.forget Λ k) :=
  BasedFunctor.ofFunctor (sourceDeformationFunctor Λ k X Y f hX hY hf)
    (sourceDeformationFunctor_comp_forget Λ k X Y f hX hY hf)

/-- The underlying ordinary functor of the based source functor is the source deformation functor. -/
theorem sourceBasedFunctor_toFunctor (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    (sourceBasedFunctor Λ k X Y f hX hY hf).toFunctor =
      sourceDeformationFunctor Λ k X Y f hX hY hf :=
  sorry

/-- The based source functor commutes strictly with the projections to the Artinian local base. -/
theorem sourceBasedFunctor_w (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    (sourceBasedFunctor Λ k X Y f hX hY hf).toFunctor ⋙
        Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)) ⋙
          FlatSchemeCat.forget Λ k =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙
        forget Λ k :=
  sorry

end FlatSchemeMorphismCat

end
