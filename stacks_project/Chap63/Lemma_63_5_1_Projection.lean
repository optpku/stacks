module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import stacks_project.Chap63.Lemma_63_5_1_LowerShriek

/-!
# Projection comparison for compact-support direct image of modules

The canonical morphism
`can : f_! F ⊗ G ⟶ f_!(F ⊗ f⁻¹ G)`
of étale sheaves of `Λ`-modules, constructed from the pure-tensor rule
`(Z, s) ⊗ t ↦ (Z, s ⊗ f⁻¹ t)` on compactly supported sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace TensorProduct
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace FiniteSupport

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
variable (Λ : Type u) [CommRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [MonoidalCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [MonoidalCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [(presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).Monoidal]
variable [(presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).Monoidal]

/-- The morphism of small-étale `X`-schemes from an open of `X_V` to `X_V`. -/
def ambientHom {V : Y.Etale} (U : (baseChangeScheme f V).Opens) :
    mk (U.ι ≫ baseChangeToSource f V) ⟶ (smallEtalePullback f).obj V :=
  MorphismProperty.Over.homMk U.ι sorry

/-- The underlying scheme morphism of `ambientHom` is the open immersion of the
ambient open. -/
theorem ambientHom_left {V : Y.Etale} (U : (baseChangeScheme f V).Opens) :
    (ambientHom f U).left = U.ι :=
  sorry

/-- The image of a section of `G` on `V` in `f⁻¹ G` on an open of `X_V`. -/
def inverseImageSection (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))
    {V : Y.Etale} (U : (baseChangeScheme f V).Opens)
    (t : G.1.obj (op V)) :
    (((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology X.smallEtaleTopology).obj G).1.obj
      (op (mk (U.ι ≫ baseChangeToSource f V))) :=
  ((((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology X.smallEtaleTopology).obj G).1.map
      (ambientHom f U).op).hom
    (((((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
            Y.smallEtaleTopology X.smallEtaleTopology).unit.app G).hom.app
        (op V)).hom t)

/-- Inverse-image sections are obtained from the unit of
`sheafAdjunctionContinuous` followed by restriction along `ambientHom`. -/
theorem inverseImageSection_eq (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))
    {V : Y.Etale} (U : (baseChangeScheme f V).Opens)
    (t : G.1.obj (op V)) :
    inverseImageSection f Λ G U t =
      ((((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
              Y.smallEtaleTopology X.smallEtaleTopology).obj G).1.map
          (ambientHom f U).op).hom
        (((((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
                Y.smallEtaleTopology X.smallEtaleTopology).unit.app G).hom.app
            (op V)).hom t) :=
  sorry

/-- The canonical map from pointwise tensor of sections to sections of the sheaf
tensor. -/
def sheafTensorSectionHom
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (U : X.Etaleᵒᵖ) :
    F.1.obj U ⊗ G.1.obj U ⟶ (F ⊗ G).1.obj U :=
  ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u} Λ)).unit.app
        (F.1 ⊗ G.1)).app U ≫
    ((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).map
      ((Functor.Monoidal.μIso
            (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) F.1 G.1).inv ≫
        ((sheafificationAdjunction X.smallEtaleTopology
              (ModuleCat.{u} Λ)).counit.app F ⊗ₘ
          (sheafificationAdjunction X.smallEtaleTopology
              (ModuleCat.{u} Λ)).counit.app G :
            (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj F.1 ⊗
                (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj G.1 ⟶
              F ⊗ G))).app U

/-- The bilinear comparison `H_Z(F) ⊗ G(V) ⟶ H_Z(F ⊗ f⁻¹ G)` on pure tensors
`(s, t) ↦ s ⊗ f⁻¹ t`. -/
def moduleSectionsTensor
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) {V : Y.Etale}
    (A : Admissible f V) :
    moduleSections f Λ F A ⊗ G.1.obj (op V) ⟶
      moduleSections f Λ
        (F ⊗ ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology X.smallEtaleTopology).obj G) A :=
  ModuleCat.ofHom <| TensorProduct.lift <|
    LinearMap.mk₂ Λ
      (fun σ t ↦
        ⟨(sheafTensorSectionHom Λ F
              (((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
                  Y.smallEtaleTopology X.smallEtaleTopology).obj G)
              (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))).hom
          (σ.1 ⊗ₜ inverseImageSection f Λ G A.ambient t), sorry⟩)
      sorry sorry sorry sorry

/-- The cocone on `Z ↦ H_Z(F)` whose component at an admissible support `Z`
sends a supported section `s` to the class of `(Z, s ⊗ f⁻¹ t)`. -/
def moduleTensorCocone
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (V : Y.Etale)
    (t : G.1.obj (op V)) :
    Cocone (moduleDiagram f Λ F V) where
  pt := colimit (moduleDiagram f Λ
    (F ⊗ ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology).obj G) V)
  ι :=
    { app := fun A ↦
        ModuleCat.ofHom
            ((moduleSectionsTensor f Λ F G A).hom ∘ₗ
              (TensorProduct.mk Λ (moduleSections f Λ F A)
                (G.1.obj (op V))).flip t) ≫
          colimit.ι (moduleDiagram f Λ
            (F ⊗ ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
                Y.smallEtaleTopology X.smallEtaleTopology).obj G) V) A
      naturality := sorry }

/-- The component at `V` of the presheaf-level projection comparison, induced by
the bilinear rule sending the class of `(Z, s) ⊗ t` to the class of
`(Z, s ⊗ f⁻¹ t)`. -/
def projectionPresheafApp
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (V : Y.Etale) :
    colimit (moduleDiagram f Λ F V) ⊗ G.1.obj (op V) ⟶
      colimit (moduleDiagram f Λ
        (F ⊗ ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology X.smallEtaleTopology).obj G) V) :=
  ModuleCat.ofHom <| TensorProduct.lift <|
    LinearMap.mk₂ Λ
      (fun σ t ↦
        (colimit.desc (moduleDiagram f Λ F V)
          (moduleTensorCocone f Λ F G V t)).hom σ)
      sorry sorry sorry sorry

end FiniteSupport

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
variable (Λ : Type u) [CommRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [MonoidalCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [MonoidalCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [(presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).Monoidal]
variable [(presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).Monoidal]

/-- The presheaf-level comparison
`f_{p!} F ⊗_{p,Λ} G ⟶ f_{p!}(F ⊗ f⁻¹ G)`. -/
def lowerShriekProjectionPresheafHom
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModulePresheaf f Λ).obj F ⊗ G.1 ⟶
      (lowerShriekModulePresheaf f Λ).obj
        (F ⊗ ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology X.smallEtaleTopology).obj G) where
  app V := FiniteSupport.projectionPresheafApp f Λ F G V.unop
  naturality := sorry

/-- The component of the presheaf-level projection comparison at `V` is
`projectionPresheafApp`. -/
theorem lowerShriekProjectionPresheafHom_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (V : Y.Etale) :
    (lowerShriekProjectionPresheafHom f Λ F G).app (op V) =
      FiniteSupport.projectionPresheafApp f Λ F G V :=
  sorry

/-- The sheaf-level comparison morphism
`can : f_! F ⊗_Λ G ⟶ f_!(F ⊗_Λ f⁻¹ G)`. -/
def lowerShriekProjectionHom
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule f Λ).obj F ⊗ G ⟶
      (lowerShriekModule f Λ).obj
        (F ⊗ ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology X.smallEtaleTopology).obj G) :=
  ((lowerShriekModule f Λ).obj F ◁
      (asIso ((sheafificationAdjunction Y.smallEtaleTopology
              (ModuleCat.{u} Λ)).counit.app G)).inv) ≫
    Functor.LaxMonoidal.μ
        (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))
        ((lowerShriekModulePresheaf f Λ).obj F) G.1 ≫
    (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).map
      (lowerShriekProjectionPresheafHom f Λ F G)

/-- The sheaf-level comparison is obtained from the unit/counit of sheafification
and the presheaf-level pure-tensor rule. -/
theorem lowerShriekProjectionHom_def
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    lowerShriekProjectionHom f Λ F G =
      ((lowerShriekModule f Λ).obj F ◁
          (asIso ((sheafificationAdjunction Y.smallEtaleTopology
                  (ModuleCat.{u} Λ)).counit.app G)).inv) ≫
        Functor.LaxMonoidal.μ
          (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))
          ((lowerShriekModulePresheaf f Λ).obj F) G.1 ≫
        (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).map
          (lowerShriekProjectionPresheafHom f Λ F G) :=
  sorry

/-- The comparison `can` is an isomorphism of étale sheaves of `Λ`-modules. -/
instance lowerShriekProjectionHom_isIso [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    IsIso (lowerShriekProjectionHom f Λ F G) :=
  sorry

/-- The comparison `can` is natural in the sheaves `F` and `G`. -/
theorem lowerShriekProjectionHom_natural [LocallyOfFiniteType f]
    {F F' : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)}
    {G G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)}
    (α : F ⟶ F') (β : G ⟶ G') :
    ((lowerShriekModule f Λ).map α ⊗ₘ β) ≫
        lowerShriekProjectionHom f Λ F' G' =
      lowerShriekProjectionHom f Λ F G ≫
        (lowerShriekModule f Λ).map
          (α ⊗ₘ ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
              Y.smallEtaleTopology X.smallEtaleTopology).map β) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
