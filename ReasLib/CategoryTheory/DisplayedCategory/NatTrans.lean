/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.Functor

/-!
# Natural transformations of displayed functors

Displayed natural transformations retain the base natural transformation explicitly.  Their
components may therefore lie over non-identity base arrows, while totalization produces the
ordinary natural transformation between total-category functors.
-/

@[expose] public section

namespace CategoryTheory

universe v u v' u'

set_option linter.checkUnivs false in
/-- A natural transformation between displayed functors over a base natural transformation. -/
structure DisplayedNatTrans
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {D : DisplayedCategory C} {E : DisplayedCategory C'}
    {F G : C ⥤ C'} (Φ : DisplayedFunctor D E F) (Ψ : DisplayedFunctor D E G)
    (α : F ⟶ G) where
  /-- The displayed component over each base natural-transformation component. -/
  app : {X : C} → (x : D.obj X) →
    E.Hom (α.app X) (Φ.obj x) (Ψ.obj x)
  /-- Naturality of the displayed components, transported along base naturality. -/
  naturality : ∀ {X Y : C} {f : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
    (φ : D.Hom f x y),
    DisplayedCategory.Hom.cast E (α.naturality f)
      (E.comp (Φ.map φ) (app y)) =
        E.comp (app x) (Ψ.map φ)

namespace DisplayedNatTrans

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
variable {D : DisplayedCategory C} {E : DisplayedCategory C'}
variable {F G H : C ⥤ C'}
variable {Φ : DisplayedFunctor D E F} {Ψ : DisplayedFunctor D E G}
variable {Χ : DisplayedFunctor D E H} {α : F ⟶ G} {β : G ⟶ H}

/-- Reindex a displayed natural transformation along an equality of its base transformations. -/
def reindex {α β : F ⟶ G} (h : α = β)
    (η : DisplayedNatTrans Φ Ψ α) : DisplayedNatTrans Φ Ψ β := h ▸ η

/-- Reindexing along reflexivity leaves a displayed natural transformation unchanged. -/
@[simp]
theorem reindex_rfl {α : F ⟶ G} (η : DisplayedNatTrans Φ Ψ α) :
    reindex rfl η = η := sorry

/-- Successive reindexings combine by transitivity of equality. -/
@[simp]
theorem reindex_trans {α β γ : F ⟶ G} (h : α = β) (k : β = γ)
    (η : DisplayedNatTrans Φ Ψ α) :
    reindex k (reindex h η) = reindex (h.trans k) η := sorry

/-- Totalization of a displayed natural transformation. -/
def total (η : DisplayedNatTrans Φ Ψ α) :
    DisplayedFunctor.total Φ ⟶ DisplayedFunctor.total Ψ where
  app X := ⟨α.app X.base, η.app X.obj⟩
  naturality := sorry

/-- The base component of a totalized displayed natural transformation. -/
@[simp]
theorem total_app_base (η : DisplayedNatTrans Φ Ψ α)
    (X : DisplayedCategory.Total D) :
    ((total η).app X).base = α.app X.base := sorry

/-- The displayed component of a totalized displayed natural transformation. -/
@[simp]
theorem total_app_displayed (η : DisplayedNatTrans Φ Ψ α)
    (X : DisplayedCategory.Total D) :
    ((total η).app X).displayed = η.app X.obj := sorry

/-- Totalization forgets the proof-level presentation of a reindexed base transformation. -/
@[simp]
theorem total_reindex {α β : F ⟶ G} (h : α = β)
    (η : DisplayedNatTrans Φ Ψ α) :
    total (reindex h η) = total η := sorry

/-- The component of a reindexed displayed transformation is the canonical transport of the
original component along the corresponding base-natural-transformation equality. -/
@[simp]
theorem reindex_app {α β : F ⟶ G} (h : α = β)
    (η : DisplayedNatTrans Φ Ψ α) {X : C} (x : D.obj X) :
    (reindex h η).app x =
      DisplayedCategory.Hom.cast E
        (congrArg (fun γ : F ⟶ G => γ.app X) h) (η.app x) := sorry

/-- A totalized displayed-transformation component is canonically a hom-lift of its base
natural-transformation component. -/
instance total_app_isHomLift (η : DisplayedNatTrans Φ Ψ α)
    (X : DisplayedCategory.Total D) :
    (DisplayedCategory.Total.forget E).IsHomLift
      (α.app X.base) ((total η).app X) := sorry

/-- The identity displayed natural transformation. -/
def id (Φ : DisplayedFunctor D E F) : DisplayedNatTrans Φ Φ (𝟙 F) where
  app x := E.id (Φ.obj x)
  naturality := sorry

/-- Vertical composition of displayed natural transformations. -/
def comp (η : DisplayedNatTrans Φ Ψ α) (θ : DisplayedNatTrans Ψ Χ β) :
    DisplayedNatTrans Φ Χ (α ≫ β) where
  app x := E.comp (η.app x) (θ.app x)
  naturality := sorry

/-- Displayed natural transformations are determined by their displayed components. -/
@[ext]
theorem ext {η θ : DisplayedNatTrans Φ Ψ α}
    (h : ∀ {X : C} (x : D.obj X), η.app x = θ.app x) : η = θ := sorry

/-- The identity component computes to the displayed identity. -/
@[simp]
theorem id_app (Φ : DisplayedFunctor D E F) {X : C} (x : D.obj X) :
    (id Φ).app x = E.id (Φ.obj x) := sorry

/-- A composite component computes to the displayed composite. -/
@[simp]
theorem comp_app (η : DisplayedNatTrans Φ Ψ α) (θ : DisplayedNatTrans Ψ Χ β)
    {X : C} (x : D.obj X) :
    (comp η θ).app x = E.comp (η.app x) (θ.app x) := sorry

/-- Reindexing commutes with vertical composition. -/
@[simp]
theorem comp_reindex {α α' : F ⟶ G} {β β' : G ⟶ H}
    (h : α = α') (k : β = β')
    (η : DisplayedNatTrans Φ Ψ α) (θ : DisplayedNatTrans Ψ Χ β) :
    reindex (congrArg₂ (fun a b => a ≫ b) h k) (comp η θ) =
      comp (reindex h η) (reindex k θ) := sorry

/-- The identity displayed transformation is a left unit up to base-transformation transport. -/
@[simp]
theorem id_comp {α : F ⟶ G} (η : DisplayedNatTrans Φ Ψ α) :
    reindex (Category.id_comp α) (comp (id Φ) η) = η := sorry

/-- The identity displayed transformation is a right unit up to base-transformation transport. -/
@[simp]
theorem comp_id {α : F ⟶ G} (η : DisplayedNatTrans Φ Ψ α) :
    reindex (Category.comp_id α) (comp η (id Ψ)) = η := sorry

/-- Displayed vertical composition is associative up to base-transformation transport. -/
@[simp]
theorem assoc {I : C ⥤ C'} {α : F ⟶ G} {β : G ⟶ H} {γ : H ⟶ I}
    {Ω : DisplayedFunctor D E I}
    (η : DisplayedNatTrans Φ Ψ α)
    (θ : DisplayedNatTrans Ψ Χ β)
    (κ : DisplayedNatTrans Χ Ω γ) :
    reindex (Category.assoc α β γ) (comp (comp η θ) κ) =
      comp η (comp θ κ) := sorry

/-- Vertical composition normalized to the identity base transformation. -/
def vcomp {F : C ⥤ C'} {Φ Ψ Χ : DisplayedFunctor D E F}
    (η : DisplayedNatTrans Φ Ψ (𝟙 F))
    (θ : DisplayedNatTrans Ψ Χ (𝟙 F)) :
    DisplayedNatTrans Φ Χ (𝟙 F) :=
  reindex (Category.comp_id (𝟙 F)) (comp η θ)

/-- The component of normalized vertical composition is the transported displayed composite. -/
@[simp]
theorem vcomp_app {F : C ⥤ C'} {Φ Ψ Χ : DisplayedFunctor D E F}
    (η : DisplayedNatTrans Φ Ψ (𝟙 F))
    (θ : DisplayedNatTrans Ψ Χ (𝟙 F)) {X : C} (x : D.obj X) :
    (vcomp η θ).app x =
      DisplayedCategory.Hom.cast E (Category.comp_id (𝟙 (F.obj X)))
        (E.comp (η.app x) (θ.app x)) := sorry

/-- The identity displayed transformation is a left unit for normalized vertical composition. -/
@[simp]
theorem id_vcomp {F : C ⥤ C'} {Φ Ψ : DisplayedFunctor D E F}
    (η : DisplayedNatTrans Φ Ψ (𝟙 F)) :
    vcomp (id Φ) η = η := sorry

/-- The identity displayed transformation is a right unit for normalized vertical composition. -/
@[simp]
theorem vcomp_id {F : C ⥤ C'} {Φ Ψ : DisplayedFunctor D E F}
    (η : DisplayedNatTrans Φ Ψ (𝟙 F)) :
    vcomp η (id Ψ) = η := sorry

/-- Normalized vertical composition is associative. -/
@[simp]
theorem vcomp_assoc {F : C ⥤ C'}
    {Φ Ψ Χ Ω : DisplayedFunctor D E F}
    (η : DisplayedNatTrans Φ Ψ (𝟙 F))
    (θ : DisplayedNatTrans Ψ Χ (𝟙 F))
    (κ : DisplayedNatTrans Χ Ω (𝟙 F)) :
    vcomp (vcomp η θ) κ = vcomp η (vcomp θ κ) := sorry

/-- Totalization preserves normalized vertical composition. -/
@[simp]
theorem total_vcomp {F : C ⥤ C'} {Φ Ψ Χ : DisplayedFunctor D E F}
    (η : DisplayedNatTrans Φ Ψ (𝟙 F))
    (θ : DisplayedNatTrans Ψ Χ (𝟙 F)) :
    total (vcomp η θ) = total η ≫ total θ := sorry

/-- Totalization preserves the identity displayed natural transformation. -/
@[simp]
theorem total_id (Φ : DisplayedFunctor D E F) :
    total (id Φ) = 𝟙 (DisplayedFunctor.total Φ) := sorry

/-- Totalization preserves vertical composition of displayed natural transformations. -/
@[simp]
theorem total_comp (η : DisplayedNatTrans Φ Ψ α) (θ : DisplayedNatTrans Ψ Χ β) :
    total (comp η θ) = total η ≫ total θ := sorry

end DisplayedNatTrans

end CategoryTheory
