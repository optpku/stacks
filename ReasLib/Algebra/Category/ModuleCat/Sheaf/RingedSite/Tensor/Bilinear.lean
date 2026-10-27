/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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

universe u v w

namespace SheafOfModules.RingedSite

section General

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (O : Sheaf J CommRingCat.{w})

/-- A restriction-compatible bilinear map on local sections of three module sheaves. -/
@[stacks 03L6 "bilinear maps on sections of module sheaves"]
abbrev BilinearMap
    (F G H : ringedSiteModuleCategory.{u, v, w, w} J O) :=
  PresheafOfModules.BilinearMap O.obj F.val G.val H.val

namespace BilinearMap

variable {O}
variable {F G H : ringedSiteModuleCategory.{u, v, w, w} J O}

/-- Compatible bilinear maps on local sections are canonically equivalent to morphisms from the
tensor product sheaf. -/
@[stacks 03L6 "bilinear universal property for module sheaves"]
noncomputable def homEquiv :
    BilinearMap O F G H ≃ (tensorObj F G ⟶ H) :=
  (PresheafOfModules.BilinearMap.homEquiv
      (R := O.obj) (F := F.val) (G := G.val) (H := H.val)).trans
    ((moduleSheafificationHomEquiv O
        (PresheafOfModules.Monoidal.tensorObj F.val G.val) H).symm.trans
      ((ModuleSheafification.tensorObjIso O F G).symm.homCongr (Iso.refl H)))

/-- The tensor-product sheaf morphism represented by a compatible sectionwise bilinear map. -/
@[stacks 03L6 "descent of a sectionwise bilinear map"]
noncomputable def hom (b : BilinearMap O F G H) : tensorObj F G ⟶ H :=
  homEquiv b

/-- The compatible sectionwise bilinear map represented by a tensor-product sheaf morphism. -/
noncomputable def ofHom (f : tensorObj F G ⟶ H) : BilinearMap O F G H :=
  homEquiv.symm f

section Underlying

variable [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/-- A sectionwise bilinear map as an actual morphism of the underlying sheaves of sets. -/
noncomputable def underlyingHom (b : BilinearMap O F G H) :
    (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J O)).obj F ⊗
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J O)).obj G ⟶
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J O)).obj H where
  hom :=
    { app := fun U ↦ TypeCat.ofHom fun p ↦ b.app U p.1 p.2
      naturality := by sorry }

/-- Evaluate the specified sheaf map while retaining the module carriers for inference. -/
noncomputable def underlyingApp
    (b : (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J O)).obj F ⊗
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J O)).obj G ⟶
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J O)).obj H)
    (U : Cᵒᵖ) : F.val.obj U → G.val.obj U → H.val.obj U :=
  fun x y ↦ b.hom.app U (x, y)

/-- Lift a specified sheaf morphism to the existing sectionwise bilinear-map type.
Only its additivity and scalar compatibility are supplied as proof fields. -/
noncomputable def ofUnderlyingHom
    (b : (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J O)).obj F ⊗
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J O)).obj G ⟶
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J O)).obj H)
    (ha : ∀ U (x x' : F.val.obj U) (y : G.val.obj U),
      underlyingApp b U (x + x') y = underlyingApp b U x y + underlyingApp b U x' y)
    (hs : ∀ U (r : O.obj.obj U) (x : F.val.obj U) (y : G.val.obj U),
      underlyingApp b U (r • x) y = r • underlyingApp b U x y)
    (ha' : ∀ U (x : F.val.obj U) (y y' : G.val.obj U),
      underlyingApp b U x (y + y') = underlyingApp b U x y + underlyingApp b U x y')
    (hs' : ∀ U (r : O.obj.obj U) (x : F.val.obj U) (y : G.val.obj U),
      underlyingApp b U x (r • y) = r • underlyingApp b U x y) :
    BilinearMap O F G H where
  app U :=
    { toFun := fun x ↦
        { toFun := underlyingApp b U x
          map_add' := ha' U x
          map_smul' := fun r y ↦ hs' U r x y }
      map_add' := by intros; ext y; exact ha U _ _ y
      map_smul' := by intros; ext y; exact hs U _ _ y }
  naturality := by sorry

/-- The lifted bilinear map retains the supplied section function. -/
@[simp]
theorem ofUnderlyingHom_app
    (b : (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J O)).obj F ⊗
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J O)).obj G ⟶
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J O)).obj H)
    (ha hs ha' hs') (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U) :
    (ofUnderlyingHom b ha hs ha' hs').app U x y = underlyingApp b U x y := rfl

end Underlying

end BilinearMap

end General

-- Keep the established universe arguments of the section-facing API. All
-- data is supplied by the universe-polymorphic bilinear owner above.
section Legacy

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
  BilinearMap O F G H

namespace SectionBilinearMap

variable {O}
variable {F G H : ringedSiteModuleCategory J O}

/-- Compatible bilinear maps on local sections are canonically equivalent to morphisms from the
tensor product sheaf. -/
@[stacks 03L6 "bilinear universal property for module sheaves"]
noncomputable def homEquiv :
    SectionBilinearMap O F G H ≃ (tensorObj F G ⟶ H) :=
  BilinearMap.homEquiv

/-- The tensor-product sheaf morphism represented by a compatible sectionwise bilinear map. -/
@[stacks 03L6 "descent of a sectionwise bilinear map"]
noncomputable def hom (b : SectionBilinearMap O F G H) : tensorObj F G ⟶ H :=
  BilinearMap.hom b

/-- The compatible sectionwise bilinear map represented by a tensor-product sheaf morphism. -/
noncomputable def ofHom (f : tensorObj F G ⟶ H) : SectionBilinearMap O F G H :=
  BilinearMap.ofHom f

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


end Legacy

end SheafOfModules.RingedSite
