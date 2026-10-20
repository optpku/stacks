/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra
public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic

/-!
# Global sections comparison of affine scheme deformations

The functor of deformation categories sending a flat deformation `(A, Y)` of
`Spec(P)` to the flat `A`-algebra `Γ(Y, ⊤)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace FlatSchemeCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable (Λ k) (P : Type u) [CommRing P] [Algebra k P]

/-- The structure morphism `Spec(P) ⟶ Spec(k)` of an affine scheme over the residue object. -/
def specStructureHom :
    Spec (CommRingCat.of P) ⟶
      Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier) :=
  Spec.map (CommRingCat.ofHom (algebraMap k P))

/-- `specStructureHom` is `Spec.map` of `algebraMap k P`. -/
theorem specStructureHom_spec :
    specStructureHom Λ k P = Spec.map (CommRingCat.ofHom (algebraMap k P)) :=
  rfl

/-- The structure morphism of `Spec(P)` over `k` is flat. -/
instance instFlat_specStructureHom : AlgebraicGeometry.Flat (specStructureHom Λ k P) :=
  sorry

/-- The slice projection of the deformation category of `Spec(P)` to `C_Λ`. -/
def schemeDeformationForget :
    deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P) ⥤
      ArtinianLocalAlgCat Λ k :=
  Over.forget (ofResidue Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) ⋙ forget Λ k

/-- The slice projection of the deformation category of `P` to `C_Λ`. -/
def algebraDeformationForget :
    FlatAlgebraCat.deformationCategory Λ k P ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (FlatAlgebraCat.ofResidue Λ k P) ⋙ FlatAlgebraCat.forget

/-- `schemeDeformationForget` evaluates to the stored Artinian base. -/
theorem schemeDeformationForget_obj
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    (schemeDeformationForget Λ k P).obj Y = Y.left.base :=
  rfl

/-- `algebraDeformationForget` evaluates to the stored Artinian base. -/
theorem algebraDeformationForget_obj (Q : FlatAlgebraCat.deformationCategory Λ k P) :
    (algebraDeformationForget Λ k P).obj Q = Q.left.base :=
  rfl

/-- Global functions on a flat deformation of an affine scheme are flat over its base. -/
theorem globalSectionsObj_flat
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    @Module.Flat Y.left.base.carrier Γ(Y.left.scheme, ⊤) _ _
      (@Algebra.toModule _ _ _ _ (Scheme.Hom.globalSectionsAlgebra Y.left.structureHom)) :=
  sorry

/-- The object map `(A, Y) ↦ (A, Γ(Y, ⊤))` on deformations of `Spec(P)`. -/
def globalSectionsObj
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    FlatAlgebraCat Λ k :=
  FlatAlgebraCat.of Y.left.base (Γ(Y.left.scheme, ⊤) : Type u)
    (isAlgebra := Scheme.Hom.globalSectionsAlgebra Y.left.structureHom)
    (isFlat := globalSectionsObj_flat Λ k P Y)

/-- `globalSectionsObj Y` keeps the stored Artinian base. -/
theorem globalSectionsObj_base
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    (globalSectionsObj Λ k P Y).base = Y.left.base :=
  rfl

/-- Pullback of global functions commutes with the structure maps of a deformation arrow. -/
theorem globalSectionsMap_commutes
    {src tgt : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)}
    (f : src ⟶ tgt) :
    f.left.schemeHom.appTop.hom.comp
        (algebraMap (globalSectionsObj Λ k P src).base.carrier
          (globalSectionsObj Λ k P src).algebra) =
      (algebraMap (globalSectionsObj Λ k P tgt).base.carrier
        (globalSectionsObj Λ k P tgt).algebra).comp f.left.baseHom.hom.toRingHom :=
  sorry

/-- Pullback of global functions along a deformation arrow gives a bijective tensor comparison. -/
theorem globalSectionsMap_isIso_tensor
    {src tgt : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)}
    (f : src ⟶ tgt) :
    Function.Bijective (FlatAlgebraCat.canonicalTensorMap
      (Q := globalSectionsObj Λ k P src) (P := globalSectionsObj Λ k P tgt) f.left.baseHom
      f.left.schemeHom.appTop.hom (globalSectionsMap_commutes Λ k P f)) :=
  sorry

/-- A morphism of deformations of `Spec(P)` induces the corresponding map on global sections. -/
def globalSectionsMap
    {src tgt : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)}
    (f : src ⟶ tgt) :
    globalSectionsObj Λ k P src ⟶ globalSectionsObj Λ k P tgt :=
  FlatAlgebraCat.Hom.of f.left.baseHom f.left.schemeHom.appTop.hom
    (globalSectionsMap_commutes Λ k P f) (globalSectionsMap_isIso_tensor Λ k P f)

/-- `globalSectionsMap` preserves the underlying morphism of Artinian local algebras. -/
theorem globalSectionsMap_baseHom
    {src tgt : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)}
    (f : src ⟶ tgt) :
    (globalSectionsMap Λ k P f).baseHom = f.left.baseHom :=
  rfl

/-- The special-fibre map on global functions commutes with the residue base map. -/
theorem globalSectionsResidueHom_commutes
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    ((Y.hom.schemeHom.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom).comp
        (algebraMap (globalSectionsObj Λ k P Y).base.carrier
          (globalSectionsObj Λ k P Y).algebra) =
      (algebraMap (FlatAlgebraCat.ofResidue Λ k P).base.carrier
        (FlatAlgebraCat.ofResidue Λ k P).algebra).comp Y.hom.baseHom.hom.toRingHom :=
  sorry

/-- The special-fibre map on global functions gives a bijective residue tensor comparison. -/
theorem globalSectionsResidueHom_isIso_tensor
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    Function.Bijective (FlatAlgebraCat.canonicalTensorMap
      (Q := globalSectionsObj Λ k P Y) (P := FlatAlgebraCat.ofResidue Λ k P) Y.hom.baseHom
      ((Y.hom.schemeHom.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom)
      (globalSectionsResidueHom_commutes Λ k P Y)) :=
  sorry

/-- The morphism `(A, Γ(Y, ⊤)) ⟶ (k, P)` induced by a deformation of `Spec(P)`. -/
def globalSectionsResidueHom
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    globalSectionsObj Λ k P Y ⟶ FlatAlgebraCat.ofResidue Λ k P :=
  FlatAlgebraCat.Hom.of Y.hom.baseHom
    ((Y.hom.schemeHom.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom)
    (globalSectionsResidueHom_commutes Λ k P Y)
    (globalSectionsResidueHom_isIso_tensor Λ k P Y)

/-- `globalSectionsResidueHom` uses the stored base morphism of the deformation. -/
theorem globalSectionsResidueHom_baseHom
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    (globalSectionsResidueHom Λ k P Y).baseHom = Y.hom.baseHom :=
  rfl

/-- The global-functions maps commute with the maps to the residue algebra. -/
theorem globalSectionsResidueHom_naturality
    {src tgt : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)}
    (f : src ⟶ tgt) :
    globalSectionsMap Λ k P f ≫ globalSectionsResidueHom Λ k P tgt =
      globalSectionsResidueHom Λ k P src :=
  sorry

/-- Pullback on global functions preserves identity deformation arrows. -/
theorem globalSectionsMap_id
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    globalSectionsMap Λ k P (𝟙 Y) = 𝟙 (globalSectionsObj Λ k P Y) :=
  sorry

/-- Pullback on global functions preserves composition of deformation arrows. -/
theorem globalSectionsMap_comp
    {src mid tgt : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)}
    (f : src ⟶ mid) (g : mid ⟶ tgt) :
    globalSectionsMap Λ k P (f ≫ g) =
      globalSectionsMap Λ k P f ≫ globalSectionsMap Λ k P g :=
  sorry

/-- The functor `Def_X ⥤ Def_P` sending `(A, Y)` to `(A, Γ(Y, ⊤))`. -/
def globalSectionsFunctor :
    deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P) ⥤
      FlatAlgebraCat.deformationCategory Λ k P where
  obj Y := Over.mk (globalSectionsResidueHom Λ k P Y)
  map f := Over.homMk (globalSectionsMap Λ k P f)
    (globalSectionsResidueHom_naturality Λ k P f)
  map_id Y := by
    apply Over.OverMorphism.ext
    exact globalSectionsMap_id Λ k P Y
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact globalSectionsMap_comp Λ k P f g

/-- An object of `Def_X` and its global-sections image have the same Artinian base. -/
theorem globalSectionsFunctor_obj_left_base
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    ((globalSectionsFunctor Λ k P).obj Y).left.base = Y.left.base :=
  rfl

/-- `globalSectionsFunctor` lies strictly over `C_Λ`. -/
theorem globalSectionsFunctor_comp_forget :
    globalSectionsFunctor Λ k P ⋙ algebraDeformationForget Λ k P =
      schemeDeformationForget Λ k P := by
  exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ f ↦
    ((Category.id_comp (f.left.baseHom ≫ 𝟙 _)).trans
      (Category.comp_id f.left.baseHom)).symm)

/-- The morphism of deformation categories given by global sections. -/
def globalSectionsBasedFunctor :
    BasedCategory.ofFunctor (schemeDeformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor (algebraDeformationForget Λ k P) :=
  BasedFunctor.ofFunctor (globalSectionsFunctor Λ k P) (globalSectionsFunctor_comp_forget Λ k P)

/-- The based functor of global sections commutes strictly with the projections to `C_Λ`. -/
theorem globalSectionsBasedFunctor_w :
    (globalSectionsBasedFunctor Λ k P).toFunctor ⋙ algebraDeformationForget Λ k P =
      schemeDeformationForget Λ k P :=
  (globalSectionsBasedFunctor Λ k P).w

/-- Global sections give an equivalence over the Artinian local base between deformations
of an affine scheme and deformations of its coordinate algebra. -/
instance instIsEquivalence_globalSectionsBasedFunctor :
    BasedFunctor.IsEquivalence (globalSectionsBasedFunctor Λ k P) :=
  sorry

end FlatSchemeCat
