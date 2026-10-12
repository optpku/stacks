/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import stacks_project.Chap93.Lemma_93_9_7_Algebras
public import stacks_project.Chap93.Example_93_9_1_Schemes_Deformation

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

/-- The `A`-algebra structure on `Γ(Y, ⊤)` induced by the structure morphism of
a pair `(A, Y)`. -/
abbrev algebraOfStructureHom (Y : FlatSchemeCat Λ k) :
    Algebra Y.base.carrier Γ(Y.scheme, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of Y.base.carrier)).inv ≫ Y.structureHom.appTop).hom.toAlgebra

/-- The algebra map of `algebraOfStructureHom` is `ΓSpecIso.inv ≫ structureHom.appTop`. -/
theorem algebraOfStructureHom_algebraMap (Y : FlatSchemeCat Λ k) :
    (algebraOfStructureHom Y).algebraMap =
      ((Scheme.ΓSpecIso (CommRingCat.of Y.base.carrier)).inv ≫ Y.structureHom.appTop).hom :=
  sorry

variable (Λ k) (P : Type u) [CommRing P] [Algebra k P]

/-- The structure morphism `Spec(P) ⟶ Spec(k)` of an affine scheme over the residue object. -/
def specStructureHom :
    Spec (CommRingCat.of P) ⟶
      Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier) :=
  Spec.map (CommRingCat.ofHom (algebraMap k P))

/-- `specStructureHom` is `Spec.map` of `algebraMap k P`. -/
theorem specStructureHom_spec :
    specStructureHom Λ k P = Spec.map (CommRingCat.ofHom (algebraMap k P)) :=
  sorry

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
  sorry

/-- `algebraDeformationForget` evaluates to the stored Artinian base. -/
theorem algebraDeformationForget_obj (Q : FlatAlgebraCat.deformationCategory Λ k P) :
    (algebraDeformationForget Λ k P).obj Q = Q.left.base :=
  sorry

/-- The object map `(A, Y) ↦ (A, Γ(Y, ⊤))` on deformations of `Spec(P)`. -/
def globalSectionsObj
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    FlatAlgebraCat Λ k where
  base := Y.left.base
  algebra := (Γ(Y.left.scheme, ⊤) : Type u)
  isAlgebra := algebraOfStructureHom Y.left
  isFlat := sorry

/-- `globalSectionsObj Y` keeps the stored Artinian base. -/
theorem globalSectionsObj_base
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    (globalSectionsObj Λ k P Y).base = Y.left.base :=
  sorry

/-- A morphism of deformations of `Spec(P)` induces the corresponding map on global sections. -/
def globalSectionsMap
    {src tgt : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)}
    (f : src ⟶ tgt) :
    globalSectionsObj Λ k P src ⟶ globalSectionsObj Λ k P tgt :=
  FlatAlgebraCat.Hom.of f.left.baseHom f.left.schemeHom.appTop.hom sorry sorry

/-- `globalSectionsMap` preserves the underlying morphism of Artinian local algebras. -/
theorem globalSectionsMap_baseHom
    {src tgt : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)}
    (f : src ⟶ tgt) :
    (globalSectionsMap Λ k P f).baseHom = f.left.baseHom :=
  sorry

/-- The morphism `(A, Γ(Y, ⊤)) ⟶ (k, P)` induced by a deformation of `Spec(P)`. -/
def globalSectionsResidueHom
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    globalSectionsObj Λ k P Y ⟶ FlatAlgebraCat.ofResidue Λ k P :=
  FlatAlgebraCat.Hom.of Y.hom.baseHom
    ((Y.hom.schemeHom.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom) sorry sorry

/-- `globalSectionsResidueHom` uses the stored base morphism of the deformation. -/
theorem globalSectionsResidueHom_baseHom
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    (globalSectionsResidueHom Λ k P Y).baseHom = Y.hom.baseHom :=
  sorry

/-- The functor `Def_X ⥤ Def_P` sending `(A, Y)` to `(A, Γ(Y, ⊤))`. -/
def globalSectionsFunctor :
    deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P) ⥤
      FlatAlgebraCat.deformationCategory Λ k P where
  obj Y := Over.mk (globalSectionsResidueHom Λ k P Y)
  map f := Over.homMk (globalSectionsMap Λ k P f) sorry
  map_id := sorry
  map_comp := sorry

/-- An object of `Def_X` and its global-sections image have the same Artinian base. -/
theorem globalSectionsFunctor_obj_left_base
    (Y : deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P)) :
    ((globalSectionsFunctor Λ k P).obj Y).left.base = Y.left.base :=
  sorry

/-- `globalSectionsFunctor` lies strictly over `C_Λ`. -/
theorem globalSectionsFunctor_comp_forget :
    globalSectionsFunctor Λ k P ⋙ algebraDeformationForget Λ k P =
      schemeDeformationForget Λ k P :=
  sorry

/-- The morphism of deformation categories given by global sections. -/
def globalSectionsBasedFunctor :
    BasedCategory.ofFunctor (schemeDeformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor (algebraDeformationForget Λ k P) :=
  BasedFunctor.ofFunctor (globalSectionsFunctor Λ k P) (globalSectionsFunctor_comp_forget Λ k P)

/-- The based functor of global sections commutes strictly with the projections to `C_Λ`. -/
theorem globalSectionsBasedFunctor_w :
    (globalSectionsBasedFunctor Λ k P).toFunctor ⋙ algebraDeformationForget Λ k P =
      schemeDeformationForget Λ k P :=
  sorry

end FlatSchemeCat
