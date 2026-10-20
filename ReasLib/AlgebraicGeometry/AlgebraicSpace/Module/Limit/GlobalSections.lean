/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.GlobalSections

/-!
# Colimit comparison for global sections of pullback modules

The over-category diagram consists of global sections obtained by
pulling a module back along a diagram of algebraic spaces, together with its
canonical comparison cocone at a cone point. Invertibility of the comparison
holds for directed limits with quasi-compact, quasi-separated stages and affine transitions.
-/

@[expose] public section

open CategoryTheory Limits Opposite AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}
variable {C : Type u} [Category.{v} C]
variable (D : C ⥤ AlgebraicSpace S)

/-- An over-category morphism identifies global sections after its iterated pullback with global
sections after the direct pullback. -/
theorem overPullbackModuleGlobalSections_eq
    (i₀ : C) (ℱ₀ : (D.obj i₀).Modules)
    {A B : Over i₀} (φ : A ⟶ B) :
    globalSections ((pullback (D.map (φ.left ≫ B.hom))).obj ℱ₀) =
      globalSections ((pullback (D.map A.hom)).obj ℱ₀) :=
  congrArg (fun h : A.left ⟶ i₀ ↦ globalSections ((pullback (D.map h)).obj ℱ₀)) (Over.w φ)

/-- Functoriality of `D` identifies the two maps used to form an iterated pullback of a module. -/
theorem overPullbackModuleGlobalSections_eq_map_comp
    (i₀ : C) (ℱ₀ : (D.obj i₀).Modules)
    {A B : Over i₀} (φ : A ⟶ B) :
    globalSections ((pullback (D.map φ.left ≫ D.map B.hom)).obj ℱ₀) =
      globalSections ((pullback (D.map (φ.left ≫ B.hom))).obj ℱ₀) :=
  congrArg (fun h : D.obj A.left ⟶ D.obj i₀ ↦ globalSections ((pullback h).obj ℱ₀))
    (D.map_comp φ.left B.hom).symm

/-- The transition map on global sections of pullback modules along a morphism in `Over i₀`. -/
def overPullbackModuleGlobalSectionsMap
    (i₀ : C) (ℱ₀ : (D.obj i₀).Modules)
    {A B : Over i₀} (φ : A ⟶ B) :
    globalSections ((pullback (D.map B.hom)).obj ℱ₀) ⟶
      globalSections ((pullback (D.map A.hom)).obj ℱ₀) :=
  let h := (overPullbackModuleGlobalSections_eq_map_comp D i₀ ℱ₀ φ).trans
    (overPullbackModuleGlobalSections_eq D i₀ ℱ₀ φ)
  globalSectionsPullbackComp (D.map φ.left) (D.map B.hom) ℱ₀ ≫ eqToHom h

/-- The over-category transition map on pullback-module global sections is the identity on an
identity morphism. -/
theorem overPullbackModuleGlobalSectionsMap_id
    (i₀ : C) (ℱ₀ : (D.obj i₀).Modules) (A : Over i₀) :
    overPullbackModuleGlobalSectionsMap D i₀ ℱ₀ (𝟙 A) = 𝟙 _ := sorry

/-- The over-category transition maps on pullback-module global sections respect composition. -/
theorem overPullbackModuleGlobalSectionsMap_comp
    (i₀ : C) (ℱ₀ : (D.obj i₀).Modules)
    {A B E : Over i₀} (φ : A ⟶ B) (ψ : B ⟶ E) :
    overPullbackModuleGlobalSectionsMap D i₀ ℱ₀ (φ ≫ ψ) =
      overPullbackModuleGlobalSectionsMap D i₀ ℱ₀ ψ ≫
        overPullbackModuleGlobalSectionsMap D i₀ ℱ₀ φ := sorry

/-- Pullback to a cone point through an object of `Over i₀` agrees with direct pullback along the
cone leg at `i₀`. -/
theorem limitPullbackModuleGlobalSections_eq
    (c : Cone D) (i₀ : C) (ℱ₀ : (D.obj i₀).Modules) (A : Over i₀) :
    globalSections ((pullback (c.π.app A.left ≫ D.map A.hom)).obj ℱ₀) =
      globalSections ((pullback (c.π.app i₀)).obj ℱ₀) :=
  congrArg (fun h : c.pt ⟶ D.obj i₀ ↦ globalSections ((pullback h).obj ℱ₀)) (c.w A.hom)

section
variable [UnivLE.{v, u + 1}]

/-- The over-category diagram of global sections of the pullback modules `f_a^* ℱ₀`. -/
def limitPullbackModuleGlobalSectionsDiagram
    (i₀ : C) (ℱ₀ : (D.obj i₀).Modules) :
    (Over i₀)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj A := globalSections ((pullback (D.map A.unop.hom)).obj ℱ₀)
  map φ := overPullbackModuleGlobalSectionsMap D i₀ ℱ₀ φ.unop
  map_id A := by
    simpa using overPullbackModuleGlobalSectionsMap_id D i₀ ℱ₀ A.unop
  map_comp φ ψ := by
    simpa using overPullbackModuleGlobalSectionsMap_comp D i₀ ℱ₀ ψ.unop φ.unop

/-- The map from stagewise pullback-module global sections to the pullback-module global sections
at a chosen cone point. -/
def pullbackModuleGlobalSectionsToLimitMap
    (c : Cone D) (i₀ : C) (ℱ₀ : (D.obj i₀).Modules) (A : Over i₀) :
    globalSections ((pullback (D.map A.hom)).obj ℱ₀) ⟶
      globalSections ((pullback (c.π.app i₀)).obj ℱ₀) :=
  let h := limitPullbackModuleGlobalSections_eq D c i₀ ℱ₀ A
  globalSectionsPullbackComp (c.π.app A.left) (D.map A.hom) ℱ₀ ≫ eqToHom h

/-- The comparison maps from stagewise pullback-module sections to the cone-point sections are
natural for over-category transitions. -/
theorem pullbackModuleGlobalSectionsToLimitMap_naturality
    (c : Cone D) (i₀ : C) (ℱ₀ : (D.obj i₀).Modules)
    {A B : Over i₀} (φ : A ⟶ B) :
    pullbackModuleGlobalSectionsToLimitMap D c i₀ ℱ₀ B =
      overPullbackModuleGlobalSectionsMap D i₀ ℱ₀ φ ≫
        pullbackModuleGlobalSectionsToLimitMap D c i₀ ℱ₀ A := sorry

/-- The cocone from the over-category diagram of pullback-module global sections to the global
sections of the pullback module at a chosen cone point. -/
def limitPullbackModuleGlobalSectionsCocone
    (c : Cone D) (i₀ : C) (ℱ₀ : (D.obj i₀).Modules) :
    Cocone (limitPullbackModuleGlobalSectionsDiagram D i₀ ℱ₀) where
  pt := globalSections ((pullback (c.π.app i₀)).obj ℱ₀)
  ι :=
    { app := fun A ↦ pullbackModuleGlobalSectionsToLimitMap D c i₀ ℱ₀ A.unop
      naturality := fun A B φ ↦ by
        change overPullbackModuleGlobalSectionsMap D i₀ ℱ₀ φ.unop ≫
            pullbackModuleGlobalSectionsToLimitMap D c i₀ ℱ₀ B.unop =
          pullbackModuleGlobalSectionsToLimitMap D c i₀ ℱ₀ A.unop ≫ 𝟙 _
        rw [Category.comp_id]
        exact (pullbackModuleGlobalSectionsToLimitMap_naturality D c i₀ ℱ₀ φ.unop).symm }

/-- The canonical comparison map from the colimit of stagewise pullback-module global sections
to global sections of the pullback module at a cone point. -/
def limitPullbackModuleGlobalSectionsColimitMap
    (c : Cone D) (i₀ : C) (ℱ₀ : (D.obj i₀).Modules)
    [HasColimit (limitPullbackModuleGlobalSectionsDiagram D i₀ ℱ₀)] :
    colimit (limitPullbackModuleGlobalSectionsDiagram D i₀ ℱ₀) ⟶
      globalSections ((pullback (c.π.app i₀)).obj ℱ₀) :=
  colimit.desc (limitPullbackModuleGlobalSectionsDiagram D i₀ ℱ₀)
    (limitPullbackModuleGlobalSectionsCocone D c i₀ ℱ₀)

/-- Restricting the colimit comparison to a stage gives its canonical map to cone-point sections. -/
theorem limitPullbackModuleGlobalSectionsColimitMap_ι
    (c : Cone D) (i₀ : C) (ℱ₀ : (D.obj i₀).Modules)
    [HasColimit (limitPullbackModuleGlobalSectionsDiagram D i₀ ℱ₀)] (A : Over i₀) :
    colimit.ι (limitPullbackModuleGlobalSectionsDiagram D i₀ ℱ₀) (op A) ≫
        limitPullbackModuleGlobalSectionsColimitMap D c i₀ ℱ₀ =
      pullbackModuleGlobalSectionsToLimitMap D c i₀ ℱ₀ A :=
  colimit.ι_desc (limitPullbackModuleGlobalSectionsCocone D c i₀ ℱ₀) (op A)

end

/-- Under a directed inverse limit of quasi-compact, quasi-separated algebraic spaces with affine
transition maps, global sections of a quasi-coherent pullback module commute with the canonical
over-category colimit comparison. -/
theorem limitPullbackModuleGlobalSectionsColimitMap_isIso
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
    [∀ j : OrderDual I, IsQuasiCompact (D.obj j)]
    [∀ j : OrderDual I, IsQuasiSeparated (D.obj j)]
    [∀ {j j' : OrderDual I} (f : j ⟶ j'), Affine (D.map f)]
    (i₀ : OrderDual I) (ℱ₀ : (D.obj i₀).Modules) [ℱ₀.IsQuasicoherent] :
    IsIso (limitPullbackModuleGlobalSectionsColimitMap D c i₀ ℱ₀) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
