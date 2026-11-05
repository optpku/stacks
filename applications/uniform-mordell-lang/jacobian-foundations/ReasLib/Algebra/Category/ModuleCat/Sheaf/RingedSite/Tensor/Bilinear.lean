module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bilinear maps on sections of module sheaves

The bilinear universal property is owned by module presheaves.  This leaf transports that
equivalence through module sheafification and the canonical tensor comparison, producing the
standard equivalence between compatible sectionwise bilinear maps and tensor-product morphisms.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- A restriction-compatible bilinear map on local sections of three module sheaves. -/
@[stacks 03L6 "bilinear maps on sections of module sheaves"]
abbrev SectionBilinearMap
    (F G H : ringedSiteModuleCategory J O) :=
  PresheafOfModules.BilinearMap O.obj F.val G.val H.val

namespace SectionBilinearMap

variable {O}
variable {F G H : ringedSiteModuleCategory J O}

/-- Compatible bilinear maps on local sections are canonically equivalent to morphisms from the
tensor product sheaf. -/
@[stacks 03L6 "bilinear universal property for module sheaves"]
noncomputable def homEquiv :
    SectionBilinearMap O F G H ≃ (tensorObj F G ⟶ H) :=
  (PresheafOfModules.BilinearMap.homEquiv
      (R := O.obj) (F := F.val) (G := G.val) (H := H.val)).trans
    ((moduleSheafificationHomEquiv O
        (PresheafOfModules.Monoidal.tensorObj F.val G.val) H).symm.trans
      ((ModuleSheafification.tensorObjIso O F G).symm.homCongr (Iso.refl H)))

/-- The tensor-product sheaf morphism represented by a compatible sectionwise bilinear map. -/
@[stacks 03L6 "descent of a sectionwise bilinear map"]
noncomputable def hom (b : SectionBilinearMap O F G H) : tensorObj F G ⟶ H :=
  homEquiv b

/-- The compatible sectionwise bilinear map represented by a tensor-product sheaf morphism. -/
noncomputable def ofHom (f : tensorObj F G ⟶ H) : SectionBilinearMap O F G H :=
  homEquiv.symm f

/-- The descended sheaf morphism evaluates on a pure tensor section by the original bilinear
map. -/
@[simp]
theorem hom_tensorSection (b : SectionBilinearMap O F G H) (U : Cᵒᵖ)
    (x : F.val.obj U) (y : G.val.obj U) :
    (b.hom.val.app U).hom (tensorSection O U x y) = b.app U x y := sorry

/-- Recovering a bilinear map from a tensor morphism is evaluation on pure tensor sections. -/
@[simp]
theorem ofHom_app (f : tensorObj F G ⟶ H) (U : Cᵒᵖ)
    (x : F.val.obj U) (y : G.val.obj U) :
    (ofHom f).app U x y = (f.val.app U).hom (tensorSection O U x y) := sorry

/-- The sheaf morphism obtained from the bilinear equivalence agrees with the explicit
sheafification composite. -/
theorem hom_eq_sheafification (b : SectionBilinearMap O F G H) :
    b.hom =
      (ModuleSheafification.tensorObjIso O F G).hom ≫
        (moduleSheafification O).map b.toHom ≫
          (moduleSheafificationValIso O H).hom := sorry

/-- Converting a compatible bilinear map to a tensor morphism and back is the identity. -/
@[simp]
theorem ofHom_hom (b : SectionBilinearMap O F G H) :
    ofHom b.hom = b := sorry

/-- Converting a tensor morphism to a compatible bilinear map and back is the identity. -/
@[simp]
theorem hom_ofHom (f : tensorObj F G ⟶ H) :
    (ofHom f).hom = f := sorry

/-- Descent to a tensor-product sheaf morphism is injective. -/
theorem hom_injective :
    Function.Injective (hom : SectionBilinearMap O F G H → (tensorObj F G ⟶ H)) := sorry

/-- Morphisms from a tensor product sheaf are determined by their values on pure tensor
sections. -/
@[ext]
theorem tensorHom_ext {f g : tensorObj F G ⟶ H}
    (h : ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      (f.val.app U).hom (tensorSection O U x y) =
        (g.val.app U).hom (tensorSection O U x y)) :
    f = g := sorry

/-- Transport of a sectionwise bilinear map becomes composition with the induced tensor map. -/
theorem hom_map
    {F' G' H' : ringedSiteModuleCategory J O}
    (b : SectionBilinearMap O F G H)
    (f : F' ⟶ F) (g : G' ⟶ G) (h : H ⟶ H') :
    hom (b.map f.val g.val h.val) = tensorHom f g ≫ b.hom ≫ h := sorry

/-- Descent of sectionwise bilinear maps is natural in all three module-sheaf arguments. -/
theorem hom_naturality
    {F' G' H' : ringedSiteModuleCategory J O}
    (b : SectionBilinearMap O F G H) (b' : SectionBilinearMap O F' G' H')
    (f : F ⟶ F') (g : G ⟶ G') (h : H ⟶ H')
    (w : ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      (h.val.app U).hom (b.app U x y) =
        b'.app U ((f.val.app U).hom x) ((g.val.app U).hom y)) :
    tensorHom f g ≫ b'.hom = b.hom ≫ h := sorry

end SectionBilinearMap

end SheafOfModules.RingedSite


