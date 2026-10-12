/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Category.TopCat.Limits.Cofiltered
public import Mathlib.Topology.Spectral.Basic
public import ReasLib.Topology.Sheaves.Pullback.Sections

/-!
# Sections of pullbacks over inverse limits

This module constructs the canonical comparison from sections pulled back from stages of an
inverse system of spaces to sections pulled back to its limit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u v w

namespace TopCat.Sheaf.InverseLimit

variable {C : Type (w + 1)} [Category.{w} C]
variable {FC : C → C → Type w} {CC : C → Type w}
variable [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{w} C FC]
variable [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable {I : Type u} [Category.{v} I]
variable (F : I ⥤ TopCat.{w})

section

variable [HasLimit F]

/-- The map from a stagewise pullback section to the pullback section on the limit space. -/
noncomputable def pullbackSectionToLimitMap {i : I}
    (𝒢 : (F.obj i).Sheaf C)
    (U : CompactOpens (F.obj i)) (A : Over i) :
    ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (F.map A.hom)).obj U.toOpens)) ⟶
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (limit.π F i)).obj U.toOpens)) :=
  PullbackSections.iteratedMap (limit.π F A.left) (F.map A.hom) 𝒢 U.toOpens ≫
    eqToHom (congrArg
      (fun k : limit F ⟶ F.obj i ↦
        ((((k⁻¹).obj 𝒢).presheaf).obj (op ((Opens.map k).obj U.toOpens))))
      (limit.w F A.hom))

/-- Stagewise comparison maps to the limit are compatible with the over-category transitions. -/
theorem pullbackSectionToLimitMap_naturality {i : I}
    (𝒢 : (F.obj i).Sheaf C)
    (U : CompactOpens (F.obj i))
    {A B : Over i} (φ : A ⟶ B) :
    PullbackSections.overMap F 𝒢 U.toOpens φ ≫ pullbackSectionToLimitMap F 𝒢 U A =
      (pullbackSectionToLimitMap F 𝒢 U B :
        ((((F.map B.hom)⁻¹).obj 𝒢).presheaf).obj
            (op ((Opens.map (F.map B.hom)).obj U.toOpens)) ⟶
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
            (op ((Opens.map (limit.π F i)).obj U.toOpens))) := sorry

/-- The legs from stagewise sections to the limit pullback satisfy the cocone naturality law. -/
theorem pullbackSectionCocone_naturality {i : I}
    (𝒢 : (F.obj i).Sheaf C)
    (U : CompactOpens (F.obj i)) {A B : (Over i)ᵒᵖ} (φ : A ⟶ B) :
    (PullbackSections.over F i 𝒢 U.toOpens).map φ ≫
        pullbackSectionToLimitMap F 𝒢 U B.unop =
      pullbackSectionToLimitMap F 𝒢 U A.unop ≫
        ((Functor.const (Over i)ᵒᵖ).obj
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
            (op ((Opens.map (limit.π F i)).obj U.toOpens)))).map φ := sorry

/-- The cocone from stagewise pullback sections to pullback sections on the limit space. -/
noncomputable def pullbackSectionCocone (i : I)
    (𝒢 : (F.obj i).Sheaf C)
    (U : CompactOpens (F.obj i)) :
    Cocone (PullbackSections.over F i 𝒢 U.toOpens) where
  pt := ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
    (op ((Opens.map (limit.π F i)).obj U.toOpens))
  ι :=
    { app := fun A ↦ pullbackSectionToLimitMap F 𝒢 U A.unop
      naturality := fun {_ _} f ↦ pullbackSectionCocone_naturality F 𝒢 U f }

/-- The canonical map from the colimit of stagewise pullback sections to the pullback sections
on the limit space. -/
noncomputable def pullbackSectionColimitComparison (i : I)
    (𝒢 : (F.obj i).Sheaf C)
    (U : CompactOpens (F.obj i))
    [HasColimit (PullbackSections.over F i 𝒢 U.toOpens)] :
    colimit (PullbackSections.over F i 𝒢 U.toOpens) ⟶
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (limit.π F i)).obj U.toOpens)) :=
  colimit.desc (PullbackSections.over F i 𝒢 U.toOpens) (pullbackSectionCocone F i 𝒢 U)

/-- For a cofiltered diagram of spectral spaces with spectral transition maps, the comparison
from the colimit of pulled-back sections over a compact open to the sections on the limit pullback
is an isomorphism. -/
theorem pullbackSectionColimitComparison_isIso [IsCofiltered I]
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a)) (i : I)
    (𝒢 : (F.obj i).Sheaf C)
    (U : CompactOpens (F.obj i))
    [HasColimit (PullbackSections.over (C := C) F i 𝒢 U.toOpens)] :
    IsIso (pullbackSectionColimitComparison (C := C) F i 𝒢 U) := sorry

end

end TopCat.Sheaf.InverseLimit
