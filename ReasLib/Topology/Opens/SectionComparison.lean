/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.Over
public import ReasLib.Topology.Opens.Subspace

/-!
# Section comparison for sheaves on open subspaces

This module provides canonical isomorphisms between sections of a sheaf pulled back to an open
subspace and sections of the original sheaf on the corresponding ambient open.

The main constructions:
- `sectionIso`: pulling back a sheaf on `X` to `U` and evaluating on `W ≤ U` ≅ evaluating on `W`
- `pullbackSectionIso`: the same for the categorical pullback (requiring concrete-category hypotheses)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open TopologicalSpace.Opens TopCat.Opens.Subspace

noncomputable section

universe w v u

namespace TopCat.Opens.Subspace.Section

variable {X : TopCat.{w}}

/-- Pulling an ambient sheaf back to `U` with the open-embedding model and evaluating on `W ≤ U`
gives the ambient section object over `W`. -/
theorem objEq {C : Type u} [Category.{w} C]
    (F : TopCat.Sheaf C X) {W U : Opens X} (hWU : W ≤ U) :
    ((U.isOpenEmbedding.sheafPullback C).obj F).1.obj (op (subspaceOpenOfLE hWU)) =
      F.1.obj (op W) := sorry

/-- The canonical comparison isomorphism between restriction-to-subspace and ambient sections. -/
noncomputable def iso {C : Type u} [Category.{w} C]
    (F : TopCat.Sheaf C X) {W U : Opens X} (hWU : W ≤ U) :
    ((U.isOpenEmbedding.sheafPullback C).obj F).1.obj (op (subspaceOpenOfLE hWU)) ≅
      F.1.obj (op W) :=
  eqToIso (objEq F hWU)

/-- The section comparison commutes with restriction between represented opens. -/
theorem iso_naturality {C : Type u} [Category.{w} C]
    (F : TopCat.Sheaf C X) {W V U : Opens X}
    (hWU : W ≤ U) (hVU : V ≤ U) (hWV : W ≤ V) :
    ((U.isOpenEmbedding.sheafPullback C).obj F).1.map (subspaceOpenHom hWU hVU hWV).op ≫
      (iso F hWU).hom =
    (iso F hVU).hom ≫ F.1.map (CategoryTheory.homOfLE hWV).op := sorry

/-- Evaluating the open-embedding pullback along `B ≤ D` on `A ≤ B` recovers sections over the
same ambient open in `D`. -/
theorem homOfLE_objEq {C : Type u} [Category.{w} C]
    {A B D : Opens X} (hAB : A ≤ B) (hBD : B ≤ D)
    (F : TopCat.Sheaf C (space D)) :
    ((homOfLE_isOpenEmbedding hBD).sheafPullback C).obj F |>.1.obj
        (op (subspaceOpenOfLE hAB)) =
      F.1.obj (op (subspaceOpenOfLE (hAB.trans hBD))) := sorry

/-- The canonical section comparison for the open-embedding pullback along `B ≤ D`. -/
noncomputable def homOfLE_iso {C : Type u} [Category.{w} C]
    {A B D : Opens X} (hAB : A ≤ B) (hBD : B ≤ D)
    (F : TopCat.Sheaf C (space D)) :
    ((homOfLE_isOpenEmbedding hBD).sheafPullback C).obj F |>.1.obj
        (op (subspaceOpenOfLE hAB)) ≅
      F.1.obj (op (subspaceOpenOfLE (hAB.trans hBD))) :=
  eqToIso (homOfLE_objEq hAB hBD F)

/-- The section comparison for an open-subspace inclusion commutes with restriction. -/
theorem homOfLE_iso_naturality {C : Type u} [Category.{w} C]
    {A₁ A₂ B D : Opens X} (hA₁ : A₁ ≤ B) (hA₂ : A₂ ≤ B)
    (h12 : A₁ ≤ A₂) (hBD : B ≤ D)
    (F : TopCat.Sheaf C (space D)) :
    (((homOfLE_isOpenEmbedding hBD).sheafPullback C).obj F).1.map
        (subspaceOpenHom hA₁ hA₂ h12).op ≫
      (homOfLE_iso hA₁ hBD F).hom =
    (homOfLE_iso hA₂ hBD F).hom ≫
      F.1.map (subspaceOpenHom (hA₁.trans hBD) (hA₂.trans hBD) h12).op := sorry

/-- The section comparison is natural in the sheaf. -/
theorem homOfLE_iso_map_naturality {C : Type u} [Category.{w} C]
    {A B D : Opens X} (hAB : A ≤ B) (hBD : B ≤ D)
    {F G : TopCat.Sheaf C (space D)} (η : F ⟶ G) :
    (((homOfLE_isOpenEmbedding hBD).sheafPullback C).map η).hom.app
        (op (subspaceOpenOfLE hAB)) ≫
      (homOfLE_iso hAB hBD G).hom =
    (homOfLE_iso hAB hBD F).hom ≫
      η.hom.app (op (subspaceOpenOfLE (hAB.trans hBD))) := sorry

/-- Pullback of a sheaf morphism along an open-subspace inclusion is conjugation by the
section-comparison isomorphisms. -/
theorem homOfLE_iso_map_conjugate {C : Type u} [Category.{w} C]
    {A B D : Opens X} (hAB : A ≤ B) (hBD : B ≤ D)
    {F G : TopCat.Sheaf C (space D)} (η : F ⟶ G) :
    (homOfLE_iso hAB hBD F).hom ≫
        η.hom.app (op (subspaceOpenOfLE (hAB.trans hBD))) ≫
      (homOfLE_iso hAB hBD G).inv =
    (((homOfLE_isOpenEmbedding hBD).sheafPullback C).map η).hom.app
      (op (subspaceOpenOfLE hAB)) := sorry

end TopCat.Opens.Subspace.Section

section Pullback

variable {X : TopCat.{w}}
variable {C : Type u} [Category.{w} C]
variable {FC : C → C → Type v} {CC : C → Type w}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]
variable [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]

open TopCat.Opens.Subspace.Section

/-- The canonical pullback along `B ≤ D`, evaluated on `A ≤ B`, agrees with evaluation on the
same represented open in `D`. -/
noncomputable def TopCat.Opens.Subspace.Section.pullbackIso
    {A B D : Opens X} (hAB : A ≤ B) (hBD : B ≤ D)
    (F : TopCat.Sheaf C (TopCat.Opens.Subspace.space D)) :
    ((TopCat.Sheaf.pullback C (TopCat.Opens.Subspace.homOfLE hBD)).obj F).1.obj
        (op (TopCat.Opens.Subspace.subspaceOpenOfLE hAB)) ≅
      F.1.obj (op (TopCat.Opens.Subspace.subspaceOpenOfLE (hAB.trans hBD))) :=
  (((TopCat.Sheaf.forget C (TopCat.Opens.Subspace.space B)).mapIso
      (((TopCat.Opens.Subspace.homOfLE_isOpenEmbedding hBD).sheafPullbackIso C).app F)).app
        (op (TopCat.Opens.Subspace.subspaceOpenOfLE hAB))) ≪≫
    homOfLE_iso hAB hBD F

/-- Pullback of a sheaf morphism along `B ≤ D` is conjugation by the canonical section
comparisons. -/
theorem TopCat.Opens.Subspace.Section.pullbackIso_map_conjugate
    {A B D : Opens X} (hAB : A ≤ B) (hBD : B ≤ D)
    {F G : TopCat.Sheaf C (TopCat.Opens.Subspace.space D)} (η : F ⟶ G) :
    (pullbackIso hAB hBD F).hom ≫
        η.hom.app (op (TopCat.Opens.Subspace.subspaceOpenOfLE (hAB.trans hBD))) ≫
      (pullbackIso hAB hBD G).inv =
    ((TopCat.Sheaf.pullback C (TopCat.Opens.Subspace.homOfLE hBD)).map η).hom.app
      (op (TopCat.Opens.Subspace.subspaceOpenOfLE hAB)) := sorry

end Pullback

/-- The counit of presheaf pullback followed by pushforward along an open-subspace inclusion is
an isomorphism. -/
theorem TopCat.Opens.Subspace.presheafPullbackPushforwardCounit_isIso
    {X : TopCat.{w}} {C : Type u} [Category.{w} C] [HasColimits C] (U : Opens X) :
    IsIso (TopCat.Presheaf.pullbackPushforwardAdjunction C
      (TopCat.Opens.Subspace.inclusion U)).counit := sorry

/-- The counit of sheaf pullback followed by pushforward along an open-subspace inclusion is an
isomorphism. -/
theorem TopCat.Opens.Subspace.sheafPullbackPushforwardCounit_isIso
    {X : TopCat.{w}} {C : Type u} [Category.{w} C] {FC : C → C → Type v} {CC : C → Type w}
    [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{w} C FC]
    [HasColimits C] [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms] (U : Opens X) :
    IsIso (TopCat.Sheaf.pullbackPushforwardAdjunction C
      (TopCat.Opens.Subspace.inclusion U)).counit := sorry

end

end
