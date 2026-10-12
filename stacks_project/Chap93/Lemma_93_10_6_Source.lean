/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import stacks_project.Chap93.Example_93_9_1_Schemes_Deformation
public import stacks_project.Chap93.Example_93_10_1_Morphisms_of_schemes_Category

/-!
# Source forgetful functor of morphism deformation categories

A pair `(A, X ⟶ Y)` forgets to the source pair `(A, X)`. Restricting to residue
slices yields the canonical morphism of deformation categories
`Def_{X ⟶ Y} ⥤ᵇ Def_X` over `ArtinianLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry BasedFunctor

noncomputable section

universe u

namespace FlatSchemeMorphismCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The structure morphism over `k`, viewed as a morphism to the residue spectrum. -/
def toResidueSpec {X : Scheme.{u}}
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier) :=
  hX

/-- Flatness over `Spec k` is flatness over the residue spectrum. -/
instance instFlat_toResidueSpec {X : Scheme.{u}}
    (hX : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Flat hX] :
    AlgebraicGeometry.Flat (toResidueSpec Λ k hX) :=
  sorry

variable {Λ k}

/-- The source pair `(A, X)` attached to a morphism pair `(A, X ⟶ Y)`. -/
def sourceObj (P : FlatSchemeMorphismCat Λ k) : FlatSchemeCat Λ k :=
  FlatSchemeCat.of P.base P.source P.sourceOver

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
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    sourceObj (ofResidue Λ k X Y f hX hY hf) =
      FlatSchemeCat.ofResidue Λ k X (toResidueSpec Λ k hX) :=
  sorry

/-- The source comparison morphism `(A, X) ⟶ (A', X')` attached to `(f, g, h)`. -/
def sourceMap {src tgt : FlatSchemeMorphismCat Λ k} (φ : src ⟶ tgt) :
    sourceObj src ⟶ sourceObj tgt where
  baseHom := φ.base
  schemeHom := φ.sourceMap
  isPullback := sorry

/-- Source comparison morphisms preserve the underlying morphism of Artinian local algebras. -/
theorem sourceMap_base {src tgt : FlatSchemeMorphismCat Λ k} (φ : src ⟶ tgt) :
    (sourceMap φ).baseHom = φ.base :=
  sorry

/-- Source comparison morphisms use the stored source scheme morphism. -/
theorem sourceMap_schemeHom {src tgt : FlatSchemeMorphismCat Λ k} (φ : src ⟶ tgt) :
    (sourceMap φ).schemeHom = φ.sourceMap :=
  sorry

variable (Λ k)

/-- The ordinary forgetful functor `(A, X ⟶ Y) ↦ (A, X)` on pairs flat over `C_Λ`. -/
def sourceFunctor : FlatSchemeMorphismCat Λ k ⥤ FlatSchemeCat Λ k where
  obj := sourceObj
  map := sourceMap
  map_id := sorry
  map_comp := sorry

/-- Objects of `sourceFunctor` are the source pairs `(A, X)`. -/
theorem sourceFunctor_obj (P : FlatSchemeMorphismCat Λ k) :
    (sourceFunctor Λ k).obj P = sourceObj P :=
  sorry

/-- `sourceFunctor` lies strictly over `ArtinianLocalAlgCat`. -/
theorem sourceFunctor_comp_forget :
    sourceFunctor Λ k ⋙ FlatSchemeCat.forget Λ k = forget Λ k :=
  sorry

/-- The ordinary functor `Def_{X ⟶ Y} ⥤ Def_X` sending a deformation of `X ⟶ Y`
to the corresponding deformation of the source scheme `X`. -/
def sourceDeformationFunctor (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    deformation Λ k X Y f hX hY hf ⥤
      FlatSchemeCat.deformationCategory Λ k X (toResidueSpec Λ k hX) where
  obj ξ := Over.mk (sourceMap ξ.hom)
  map φ := Over.homMk (sourceMap φ.left) sorry
  map_id := sorry
  map_comp := sorry

/-- `sourceDeformationFunctor` lies strictly over `ArtinianLocalAlgCat`. -/
theorem sourceDeformationFunctor_comp_forget (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    sourceDeformationFunctor Λ k X Y f hX hY hf ⋙
        Over.forget
            (Fiber.fiberInclusion.obj
              (FlatSchemeCat.residueObj Λ k X (toResidueSpec Λ k hX))) ⋙
          FlatSchemeCat.forget Λ k =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙
        forget Λ k :=
  sorry

/-- The morphism `Def_{X ⟶ Y} ⥤ᵇ Def_X` of categories over `ArtinianLocalAlgCat`. -/
def sourceBasedFunctor (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙
          forget Λ k) ⥤ᵇ
      BasedCategory.ofFunctor
        (Over.forget
            (Fiber.fiberInclusion.obj
              (FlatSchemeCat.residueObj Λ k X (toResidueSpec Λ k hX))) ⋙
          FlatSchemeCat.forget Λ k) :=
  BasedFunctor.ofFunctor (sourceDeformationFunctor Λ k X Y f hX hY hf)
    (sourceDeformationFunctor_comp_forget Λ k X Y f hX hY hf)

/-- The underlying ordinary functor of `sourceBasedFunctor` is `sourceDeformationFunctor`. -/
theorem sourceBasedFunctor_toFunctor (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    (sourceBasedFunctor Λ k X Y f hX hY hf).toFunctor =
      sourceDeformationFunctor Λ k X Y f hX hY hf :=
  sorry

/-- The based source functor commutes strictly with the projections to `C_Λ`. -/
theorem sourceBasedFunctor_w (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    (sourceBasedFunctor Λ k X Y f hX hY hf).toFunctor ⋙
        Over.forget
            (Fiber.fiberInclusion.obj
              (FlatSchemeCat.residueObj Λ k X (toResidueSpec Λ k hX))) ⋙
          FlatSchemeCat.forget Λ k =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙
        forget Λ k :=
  sorry

end FlatSchemeMorphismCat

end
