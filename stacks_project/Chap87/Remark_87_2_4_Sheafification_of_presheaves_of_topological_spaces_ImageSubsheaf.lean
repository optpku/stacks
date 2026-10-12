/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Topology.Category.TopCat.Basic
public import stacks_project.Chap87.Remark_87_2_4_Sheafification_of_presheaves_of_topological_spaces_Size

/-!
# Image-generated topological subsheaf

Any map from a `TopCat`-valued presheaf into a sheaf factors through the subsheaf of
sections that lie locally in the image, equipped with the induced topology.
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

/-- Unfolding of `imageGeneratedSubfunctor`. -/
theorem imageGeneratedSubfunctor_def {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ TopCat.{max u v}} {G : Sheaf J TopCat.{max u v}} (φ : F ⟶ G.obj) :
    imageGeneratedSubfunctor φ =
      (Subfunctor.range (Functor.whiskerRight φ (forget TopCat.{max u v}))).sheafify J :=
  sorry

/-- The subsheaf `G'` of sections of `G` that lie locally in the image of `φ`, with the
induced topology on each set of sections. -/
def imageGenerated {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ TopCat.{max u v}}
    {G : Sheaf J TopCat.{max u v}} (φ : F ⟶ G.obj) : Sheaf J TopCat.{max u v} :=
  let S := imageGeneratedSubfunctor φ
  { obj :=
      { obj := fun U => TopCat.of {s : G.obj.obj U // s ∈ S.obj U}
        map := fun {U V} f =>
          TopCat.ofHom ⟨fun s => ⟨G.obj.map f s.1, S.map f s.2⟩, sorry⟩
        map_id := sorry
        map_comp := sorry }
    property := sorry }

/-- The inclusion of the image-generated subsheaf into `G`. -/
def imageGeneratedι {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ TopCat.{max u v}}
    {G : Sheaf J TopCat.{max u v}} (φ : F ⟶ G.obj) : imageGenerated φ ⟶ G :=
  Sheaf.homEquiv.symm
    { app := fun U => TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      naturality := sorry }

/-- The factorization of `φ` through `imageGenerated φ`. -/
def toImageGenerated {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ TopCat.{max u v}}
    {G : Sheaf J TopCat.{max u v}} (φ : F ⟶ G.obj) : F ⟶ (imageGenerated φ).obj where
  app U :=
    TopCat.ofHom
      ⟨fun x =>
        ⟨φ.app U x,
          (Subfunctor.range (Functor.whiskerRight φ (forget TopCat.{max u v}))).le_sheafify J U
            ⟨x, rfl⟩⟩,
        sorry⟩
  naturality := sorry

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
