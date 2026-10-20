module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation.Monoidal

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open CategoryTheory.Functor.Monoidal CategoryTheory.MonoidalCategory

universe u v

namespace ModuleCat

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- Tensor product of module-valued filtered diagrams preserves the relevant
filtered colimits in each variable. -/
instance preservesColimit₂_curriedTensor
    {R : Type u} [CommRing R]
    {J₁ J₂ : Type (max u v)} [Category J₁] [Category J₂]
    [IsFiltered J₁] [IsFiltered J₂]
    (F₁ : J₁ ⥤ ModuleCat.{max u v} R) (F₂ : J₂ ⥤ ModuleCat.{max u v} R) :
    PreservesColimit₂ F₁ F₂ (curriedTensor (ModuleCat.{max u v} R)) := sorry

/-- Applying a filtered-colimit-preserving functor to both variables preserves
the tensor-product filtered colimit. -/
instance preservesColimit₂_curriedTensor_map
    {J₁ J₂ : Type (max u v)} [Category J₁] [Category J₂]
    [IsFiltered J₁] [IsFiltered J₂]
    (G : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} G]
    (F₁ : J₁ ⥤ ModuleCat.{max u v} A) (F₂ : J₂ ⥤ ModuleCat.{max u v} A) :
    PreservesColimit₂ (F₁ ⋙ G) (F₂ ⋙ G)
      (curriedTensor (ModuleCat.{max u v} B)) := sorry

/-- A chosen filtered-colimit presentation of a module by finitely presented
modules. -/
structure FpFilteredPresentation (X : ModuleCat.{max u v} A) where
  J : Type (max u v)
  category : SmallCategory J
  filtered : IsFiltered J
  pres : @ColimitPresentation (ModuleCat.{max u v} A) inferInstance J category X
  prop_diag_obj :
    ∀ j, isFinitePresentation.{u, max u v} A
      ((@ColimitPresentation.diag (ModuleCat.{max u v} A) inferInstance J category X
          pres).obj j)

/-- Pack an existential filtered presentation by finitely presented modules into
explicit presentation data. -/
noncomputable def FpFilteredPresentation.ofExists {X : ModuleCat.{max u v} A}
    (J : Type (max u v)) [SmallCategory J] [IsFiltered J]
    (h : ∃ (pres : ColimitPresentation J X),
      ∀ j, isFinitePresentation.{u, max u v} A (pres.diag.obj j)) :
    FpFilteredPresentation.{u, v} X :=
  ⟨J, ‹SmallCategory J›, ‹IsFiltered J›, Classical.choose h, Classical.choose_spec h⟩

/-- Choose finitely presented filtered-colimit presentation data supplied by
the finite-presentation generation theorem. -/
noncomputable def fpFilteredPresentation (X : ModuleCat.{max u v} A) :
    FpFilteredPresentation.{u, v} X :=
  let h := @isFinitePresentation_ind.{u, max u v} A _ X
  let J := Classical.choose h
  let h₁ := Classical.choose_spec h
  let cat : SmallCategory J := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let filt : IsFiltered J := Classical.choose h₂
  let h₃ := Classical.choose_spec h₂
  @FpFilteredPresentation.ofExists A _ X J cat filt h₃

/-- Reinterpret a stage of an explicit finitely presented filtered presentation
as an object of the finitely presented full subcategory. -/
def FpFilteredPresentation.asFp {X : ModuleCat.{max u v} A}
    (p : FpFilteredPresentation.{u, v} X) (j : p.J) :
    (isFinitePresentation.{u, max u v} A).FullSubcategory :=
  @asFpCore X p.J p.category p.filtered p.pres p.prop_diag_obj j
where
  /-- Package one finitely presented stage as a full-subcategory object. -/
  asFpCore {X : ModuleCat.{max u v} A} (J : Type (max u v))
      [SmallCategory J] [IsFiltered J] (pres : ColimitPresentation J X)
      (prop : ∀ j, isFinitePresentation.{u, max u v} A (pres.diag.obj j))
      (j : J) : (isFinitePresentation.{u, max u v} A).FullSubcategory :=
    ⟨pres.diag.obj j, prop j⟩

/-- The filteredness and stagewise finite-presentation properties carried by an
explicit presentation. -/
theorem FpFilteredPresentation.spec {X : ModuleCat.{max u v} A}
    (p : FpFilteredPresentation.{u, v} X) :
    -- Local instance justification (proof-local temporary data): p.category interprets the dependent diagram p.pres in this presentation specification.
    letI : SmallCategory p.J := p.category
    IsFiltered p.J ∧
      ∀ j, isFinitePresentation.{u, max u v} A (p.pres.diag.obj j) := sorry

/-- Unit comparison for an extension, transported from the monoidal functor on
finitely presented modules along the restriction isomorphism. -/
def fpFilteredColimitExtension_εIso
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [F.Monoidal]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι) :
    𝟙_ (ModuleCat.{max u v} B) ≅ F'.obj (𝟙_ (ModuleCat.{max u v} A)) :=
  εIso (F ⋙ (isFinitePresentation.{v, max u v} B).ι) ≪≫
    e.symm.app (𝟙_ _)

/-- Tensorator of the extension on finitely presented modules, obtained by
conjugating the monoidal tensorator along the restriction isomorphism. -/
def fpFilteredColimitExtension_μ_fp
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [F.Monoidal]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι)
    (X Y : (isFinitePresentation.{u, max u v} A).FullSubcategory) :
    F'.obj ((isFinitePresentation.{u, max u v} A).ι.obj X) ⊗
        F'.obj ((isFinitePresentation.{u, max u v} A).ι.obj Y) ⟶
      F'.obj
        ((isFinitePresentation.{u, max u v} A).ι.obj X ⊗
          (isFinitePresentation.{u, max u v} A).ι.obj Y) :=
  ((e.app X).hom ⊗ₘ (e.app Y).hom) ≫
    (isFinitePresentation.{v, max u v} B).ι.map (μ F X Y) ≫
      (e.inv.app (X ⊗ Y))

/-- Inverse tensorator on finitely presented modules, obtained by conjugating
the oplax tensorator along the restriction isomorphism. -/
def fpFilteredColimitExtension_δ_fp
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [F.Monoidal]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι)
    (X Y : (isFinitePresentation.{u, max u v} A).FullSubcategory) :
    F'.obj
        ((isFinitePresentation.{u, max u v} A).ι.obj X ⊗
          (isFinitePresentation.{u, max u v} A).ι.obj Y) ⟶
      F'.obj ((isFinitePresentation.{u, max u v} A).ι.obj X) ⊗
        F'.obj ((isFinitePresentation.{u, max u v} A).ι.obj Y) :=
  (e.app (X ⊗ Y)).hom ≫
    (isFinitePresentation.{v, max u v} B).ι.map (δ F X Y) ≫
      (e.inv.app X ⊗ₘ e.inv.app Y)

/-- Cocone whose components are the finitely presented tensorator followed by
the maps of two filtered-colimit presentations. -/
noncomputable def fpFilteredColimitExtension_μCocone
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [F.Monoidal]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι)
    (X Y : ModuleCat.{max u v} A)
    (JX JY : Type (max u v)) [SmallCategory JX] [IsFiltered JX]
    [SmallCategory JY] [IsFiltered JY]
    (presX : ColimitPresentation JX X) (presY : ColimitPresentation JY Y)
    (propX : ∀ j, isFinitePresentation.{u, max u v} A (presX.diag.obj j))
    (propY : ∀ j, isFinitePresentation.{u, max u v} A (presY.diag.obj j)) :
    Cocone (externalProduct (presX.diag ⋙ F') (presY.diag ⋙ F')) where
  pt := F'.obj (X ⊗ Y)
  ι :=
    { app := fun jk ↦
        fpFilteredColimitExtension_μ_fp F F' e
            ⟨presX.diag.obj jk.1, propX jk.1⟩
            ⟨presY.diag.obj jk.2, propY jk.2⟩ ≫
          F'.map (presX.ι.app jk.1 ⊗ₘ presY.ι.app jk.2)
      naturality := sorry }

/-- Tensorator for an extension that preserves filtered colimits, constructed
from tensor-product colimit universal properties. -/
noncomputable def fpFilteredColimitExtension_μ
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [F.Monoidal]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (X Y : ModuleCat.{max u v} A) :
    F'.obj X ⊗ F'.obj Y ⟶ F'.obj (X ⊗ Y) :=
  @μCore X Y
    (fpFilteredPresentation X).J (fpFilteredPresentation X).category
    (fpFilteredPresentation X).filtered
    (fpFilteredPresentation Y).J (fpFilteredPresentation Y).category
    (fpFilteredPresentation Y).filtered
    (fpFilteredPresentation X).pres (fpFilteredPresentation Y).pres
    (fpFilteredPresentation X).prop_diag_obj (fpFilteredPresentation Y).prop_diag_obj
where
  /-- The tensorator obtained by descending the tensor-product cocone of two
  filtered-colimit presentations. -/
  μCore {X Y : ModuleCat.{max u v} A}
      (JX : Type (max u v)) [SmallCategory JX] [IsFiltered JX]
      (JY : Type (max u v)) [SmallCategory JY] [IsFiltered JY]
      (presX : ColimitPresentation JX X) (presY : ColimitPresentation JY Y)
      (propX : ∀ j, isFinitePresentation.{u, max u v} A (presX.diag.obj j))
      (propY : ∀ j, isFinitePresentation.{u, max u v} A (presY.diag.obj j)) :
      F'.obj X ⊗ F'.obj Y ⟶ F'.obj (X ⊗ Y) :=
    (IsColimit.tensor₂
        (isColimitOfPreserves F' presX.isColimit)
        (isColimitOfPreserves F' presY.isColimit)).desc
      (fpFilteredColimitExtension_μCocone F F' e X Y JX JY presX presY propX propY)

/-- Inverse tensorator for an extension, obtained from the tensor of chosen
filtered presentations and the oplax tensorator on finite stages. -/
noncomputable def fpFilteredColimitExtension_δ
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [F.Monoidal]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (X Y : ModuleCat.{max u v} A) :
    F'.obj (X ⊗ Y) ⟶ F'.obj X ⊗ F'.obj Y :=
  @δCore X Y
    (fpFilteredPresentation X).J (fpFilteredPresentation X).category
    (fpFilteredPresentation X).filtered
    (fpFilteredPresentation Y).J (fpFilteredPresentation Y).category
    (fpFilteredPresentation Y).filtered
    (fpFilteredPresentation X).pres (fpFilteredPresentation Y).pres
    (fpFilteredPresentation X).prop_diag_obj (fpFilteredPresentation Y).prop_diag_obj
where
  /-- The inverse tensorator obtained by descending the tensor-product cocone of
  two filtered-colimit presentations. -/
  δCore {X Y : ModuleCat.{max u v} A}
      (JX : Type (max u v)) [SmallCategory JX] [IsFiltered JX]
      (JY : Type (max u v)) [SmallCategory JY] [IsFiltered JY]
      (presX : ColimitPresentation JX X) (presY : ColimitPresentation JY Y)
      (propX : ∀ j, isFinitePresentation.{u, max u v} A (presX.diag.obj j))
      (propY : ∀ j, isFinitePresentation.{u, max u v} A (presY.diag.obj j)) :
      F'.obj (X ⊗ Y) ⟶ F'.obj X ⊗ F'.obj Y :=
    (isColimitOfPreserves F' (IsColimit.tensor₂ presX.isColimit presY.isColimit)).desc
      { pt := F'.obj X ⊗ F'.obj Y
        ι :=
          { app := fun jk ↦
              fpFilteredColimitExtension_δ_fp F F' e
                  ⟨presX.diag.obj jk.1, propX jk.1⟩
                  ⟨presY.diag.obj jk.2, propY jk.2⟩ ≫
                (F'.map (presX.ι.app jk.1) ⊗ₘ F'.map (presY.ι.app jk.2))
            naturality := sorry } }

/-- The monoidal structure on a filtered-colimit-preserving extension induced by
the monoidal structure on its finitely presented restriction. -/
@[reducible]
noncomputable def fpFilteredColimitExtension_monoidal
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [F.Monoidal]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F'] :
    F'.Monoidal where
  ε := (fpFilteredColimitExtension_εIso F F' e).hom
  η := (fpFilteredColimitExtension_εIso F F' e).inv
  μ := fpFilteredColimitExtension_μ F F' e
  δ := fpFilteredColimitExtension_δ F F' e
  μ_natural_left := sorry
  μ_natural_right := sorry
  associativity := sorry
  left_unitality := sorry
  right_unitality := sorry
  δ_natural_left := sorry
  δ_natural_right := sorry
  oplax_associativity := sorry
  oplax_left_unitality := sorry
  oplax_right_unitality := sorry
  ε_η := sorry
  η_ε := sorry
  μ_δ := sorry
  δ_μ := sorry

/-- The unit comparison of the extension has the expected inverse composite. -/
theorem fpFilteredColimitExtension_εIso_hom_inv_id
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [F.Monoidal]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι) :
    (fpFilteredColimitExtension_εIso F F' e).hom ≫
      (fpFilteredColimitExtension_εIso F F' e).inv = 𝟙 _ := sorry

/-- The extension tensorator restricts to the conjugated finite-stage
tensorator. -/
theorem fpFilteredColimitExtension_μ_restrict
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [F.Monoidal]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (X Y : (isFinitePresentation.{u, max u v} A).FullSubcategory) :
    fpFilteredColimitExtension_μ F F' e
        ((isFinitePresentation.{u, max u v} A).ι.obj X)
        ((isFinitePresentation.{u, max u v} A).ι.obj Y) =
      fpFilteredColimitExtension_μ_fp F F' e X Y := sorry

/-- The extension tensorator followed by its inverse tensorator is the identity. -/
theorem fpFilteredColimitExtension_μ_comp_δ
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [F.Monoidal]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (X Y : ModuleCat.{max u v} A) :
    fpFilteredColimitExtension_μ F F' e X Y ≫
      fpFilteredColimitExtension_δ F F' e X Y = 𝟙 _ := sorry

end ModuleCat
