module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Topology.Category.TopCat.Basic
public import ReasLib.CategoryTheory.Sites.TopCat.Size

/-!
# Image-generated topological subsheaves and sheafification

A morphism from a presheaf of topological spaces to a sheaf factors through
the subsheaf of sections locally in its image, with induced topologies.
-/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]

/-- The type-valued subpresheaf of sections of `G` that lie locally in the image of `φ`. -/
def imageGeneratedSubfunctor {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ TopCat.{max u v}} {G : Sheaf J TopCat.{max u v}}
    (φ : F ⟶ G.obj) : Subfunctor (G.obj ⋙ forget TopCat.{max u v}) :=
  (Subfunctor.range (Functor.whiskerRight φ (forget TopCat.{max u v}))).sheafify J

/-- The locally image-generated subfunctor is the sheafification of the range of `φ`. -/
theorem imageGeneratedSubfunctor_def {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ TopCat.{max u v}} {G : Sheaf J TopCat.{max u v}} (φ : F ⟶ G.obj) :
    imageGeneratedSubfunctor φ =
      (Subfunctor.range (Functor.whiskerRight φ (forget TopCat.{max u v}))).sheafify J :=
  sorry

/-- The subsheaf of sections of `G` locally in the image of `φ`, with the
induced topology on each set of sections. -/
def imageGenerated {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ TopCat.{max u v}}
    {G : Sheaf J TopCat.{max u v}} (φ : F ⟶ G.obj) : Sheaf J TopCat.{max u v} :=
  let S := imageGeneratedSubfunctor φ
  { obj :=
      { obj := fun U => TopCat.of {s : G.obj.obj U // s ∈ S.obj U}
        map := fun {U V} f =>
          TopCat.ofHom ⟨fun s => ⟨G.obj.map f s.1, S.map f s.2⟩,
            ((G.obj.map f).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
        map_id := by
          intro U
          apply TopCat.ext
          intro element
          apply Subtype.ext
          change G.obj.map (𝟙 U) element.val = element.val
          rw [G.obj.map_id]
          rfl
        map_comp := by
          intro U V W first second
          apply TopCat.ext
          intro element
          apply Subtype.ext
          change G.obj.map (first ≫ second) element.val =
            G.obj.map second (G.obj.map first element.val)
          rw [G.obj.map_comp]
          rfl }
    property := sorry }

/-- The inclusion of the image-generated subsheaf into `G`. -/
def imageGeneratedι {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ TopCat.{max u v}}
    {G : Sheaf J TopCat.{max u v}} (φ : F ⟶ G.obj) : imageGenerated φ ⟶ G :=
  Sheaf.homEquiv.symm
    { app := fun U => TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      naturality := by
        intro U V restriction
        apply TopCat.ext
        intro element
        rfl }

/-- The factorization of `φ` through `imageGenerated φ`. -/
def toImageGenerated {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ TopCat.{max u v}}
    {G : Sheaf J TopCat.{max u v}} (φ : F ⟶ G.obj) : F ⟶ (imageGenerated φ).obj where
  app U :=
    TopCat.ofHom
      ⟨fun x =>
        ⟨φ.app U x,
          (Subfunctor.range (Functor.whiskerRight φ (forget TopCat.{max u v}))).le_sheafify J U
            ⟨x, rfl⟩⟩,
        (φ.app U).hom.continuous.subtype_mk _⟩
  naturality := by
    intro U V restriction
    apply TopCat.ext
    intro element
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (φ.naturality restriction) element

/-- A section of `G` lies in `imageGenerated φ` if and only if it is locally in the image
of `φ` along some covering family. -/
theorem mem_imageGenerated_iff {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ TopCat.{max u v}} {G : Sheaf J TopCat.{max u v}} (φ : F ⟶ G.obj)
    {U : C} (s : G.obj.obj (op U)) :
    (∃ t : (imageGenerated φ).obj.obj (op U),
        (imageGeneratedι φ).hom.app (op U) t = s) ↔
      ∃ R : J.Cover U, ∀ I : R.Arrow, ∃ t : F.obj (op I.Y),
        φ.app (op I.Y) t = G.obj.map I.f.op s :=
  sorry

/-- A map from a presheaf into a sheaf of topological spaces factors through the
image-generated subsheaf. -/
theorem imageGenerated_factors {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ TopCat.{max u v}} {G : Sheaf J TopCat.{max u v}} (φ : F ⟶ G.obj) :
    toImageGenerated φ ≫ (imageGeneratedι φ).hom = φ :=
  sorry

/-- The size of `imageGenerated φ` is bounded by a cardinal depending only on the site
and the source presheaf `F`. -/
theorem exists_imageGenerated_size_bound (J : GrothendieckTopology C)
    (F : Cᵒᵖ ⥤ TopCat.{max u v}) :
    ∃ κ : Cardinal.{max u v},
      ∀ (G : Sheaf J TopCat.{max u v}) (φ : F ⟶ G.obj),
        topCatSize (imageGenerated φ).obj ≤ κ :=
  sorry

end CategoryTheory.Presheaf

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The inclusion of `TopCat`-valued sheaves on a site satisfies the solution set
condition. -/
theorem sheafToPresheaf_solutionSetCondition (J : GrothendieckTopology C) :
    SolutionSetCondition.{max u v} (sheafToPresheaf J TopCat.{max u v}) :=
  sorry

/-- `TopCat`-valued sheaves on a site admit sheafification: the inclusion into
presheaves is a right adjoint. -/
instance hasWeakSheafify_topCat (J : GrothendieckTopology C) :
    HasWeakSheafify J TopCat.{max u v} :=
  sorry

end CategoryTheory
