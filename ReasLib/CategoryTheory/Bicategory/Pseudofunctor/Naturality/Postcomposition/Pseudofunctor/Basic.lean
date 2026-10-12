/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.Hom

/-!
# The postcomposition pseudofunctor

The pseudofunctor induced between pseudofunctor bicategories by postcomposition
with a fixed pseudofunctor. Base-facing computation rules live in
`Postcomposition.Pseudofunctor.Computations`.
-/

@[expose] public section

universe wA vA uA wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
  {D : Type uD} [Bicategory.{wD, vD} D]

section Postcomposition

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped Pseudofunctor.StrongTrans


variable {A : Type uA} [Bicategory.{wA, vA} A]

/-- Naturality of the pointwise identity comparison for postcomposition. -/
private theorem postcompMapId_naturality
    (K : Pseudofunctor B D) (F : Pseudofunctor A B) :
    ∀ {a b : A} (f : a ⟶ b),
      (F.comp K).map f ◁ (K.mapId (F.obj b)).hom ≫
          ((StrongTrans.id (F.comp K)).naturality f).hom =
        (((StrongTrans.id F).postcomp K).naturality f).hom ≫
          (K.mapId (F.obj a)).hom ▷ (F.comp K).map f := sorry

/-- The identity comparison for postcomposition, assembled pointwise from the identity
comparison of the fixed pseudofunctor. -/
def postcompMapId
    (K : Pseudofunctor B D) (F : Pseudofunctor A B) :
    (StrongTrans.id F).postcomp K ≅
      StrongTrans.id (F.comp K) :=
  StrongTrans.isoMk
    (fun a ↦ K.mapId (F.obj a))
    (postcompMapId_naturality K F)

/-- Naturality of the pointwise composition comparison for postcomposition. -/
private theorem postcompMapComp_naturality
    (K : Pseudofunctor B D)
    {F G H : Pseudofunctor A B} (η : F ⟶ G) (θ : G ⟶ H) :
    ∀ {a b : A} (f : a ⟶ b),
      (F.comp K).map f ◁
            (K.mapComp (η.app b) (θ.app b)).hom ≫
          ((StrongTrans.vcomp (η.postcomp K)
            (θ.postcomp K)).naturality f).hom =
        (((StrongTrans.vcomp η θ).postcomp K).naturality f).hom ≫
          (K.mapComp (η.app a) (θ.app a)).hom ▷
            (H.comp K).map f := sorry

/-- The composition comparison for postcomposition, assembled pointwise from the composition
comparison of the fixed pseudofunctor. -/
def postcompMapComp
    (K : Pseudofunctor B D)
    {F G H : Pseudofunctor A B} (η : F ⟶ G) (θ : G ⟶ H) :
    (StrongTrans.vcomp η θ).postcomp K ≅
      StrongTrans.vcomp (η.postcomp K) (θ.postcomp K) :=
  StrongTrans.isoMk
    (fun a ↦ K.mapComp (η.app a) (θ.app a))
    (postcompMapComp_naturality K η θ)

/-- Explicit vertical composition in a target strong-transformation hom-category, used to
keep the scoped hom-category's universe fixed in postcomposition coherence statements. -/
private def postcompHomVcomp
    {F G : Pseudofunctor A D}
    {η θ ι : StrongTrans F G}
    (Γ : StrongTrans.Hom η θ) (Δ : StrongTrans.Hom θ ι) :
    StrongTrans.Hom η ι :=
  StrongTrans.Hom.of (StrongTrans.Modification.vcomp Γ.as Δ.as)

/-- Postcomposition is compatible with left whiskering in the functor bicategory. -/
private theorem postcompMap₂_whisker_left
    (K : Pseudofunctor B D) {F G H : Pseudofunctor A B}
    (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) :
    StrongTrans.Hom.postcomp (η ◁ Γ) K =
      postcompHomVcomp (postcompMapComp K η θ).hom
        (postcompHomVcomp
          (StrongTrans.whiskerLeft (η.postcomp K)
            (StrongTrans.Hom.postcomp Γ K))
          (postcompMapComp K η ι).inv) := sorry

/-- Postcomposition is compatible with right whiskering in the functor bicategory. -/
private theorem postcompMap₂_whisker_right
    (K : Pseudofunctor B D) {F G H : Pseudofunctor A B}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) :
    StrongTrans.Hom.postcomp (Γ ▷ ι) K =
      postcompHomVcomp (postcompMapComp K η ι).hom
        (postcompHomVcomp
          (StrongTrans.whiskerRight
            (StrongTrans.Hom.postcomp Γ K) (ι.postcomp K))
          (postcompMapComp K θ ι).inv) := sorry

/-- Postcomposition is compatible with the left unitor of the functor bicategory. -/
private theorem postcompMap₂_left_unitor
    (K : Pseudofunctor B D) {F G : Pseudofunctor A B}
    (η : F ⟶ G) :
    StrongTrans.Hom.postcomp (λ_ η).hom K =
      postcompHomVcomp
        (postcompMapComp K (StrongTrans.id F) η).hom
        (postcompHomVcomp
          (StrongTrans.whiskerRight
            (postcompMapId K F).hom (η.postcomp K))
          (StrongTrans.leftUnitor (η.postcomp K)).hom) := sorry

/-- Postcomposition is compatible with the right unitor of the functor bicategory. -/
private theorem postcompMap₂_right_unitor
    (K : Pseudofunctor B D) {F G : Pseudofunctor A B}
    (η : F ⟶ G) :
    StrongTrans.Hom.postcomp (ρ_ η).hom K =
      postcompHomVcomp
        (postcompMapComp K η (StrongTrans.id G)).hom
        (postcompHomVcomp
          (StrongTrans.whiskerLeft
            (η.postcomp K) (postcompMapId K G).hom)
          (StrongTrans.rightUnitor (η.postcomp K)).hom) := sorry

/-- Postcomposition is compatible with the associator of the functor bicategory. -/
private theorem postcompMap₂_associator
    (K : Pseudofunctor B D) {F G H I : Pseudofunctor A B}
    (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) :
    StrongTrans.Hom.postcomp (α_ η θ ι).hom K =
      postcompHomVcomp
        (postcompMapComp K (StrongTrans.vcomp η θ) ι).hom
        (postcompHomVcomp
          (StrongTrans.whiskerRight
            (postcompMapComp K η θ).hom (ι.postcomp K))
          (postcompHomVcomp
            (StrongTrans.associator
              (η.postcomp K) (θ.postcomp K) (ι.postcomp K)).hom
            (postcompHomVcomp
              (StrongTrans.whiskerLeft (η.postcomp K)
                (postcompMapComp K θ ι).inv)
              (postcompMapComp K η
                (StrongTrans.vcomp θ ι)).inv))) := sorry

variable (A) in
/-- Postcomposition by a fixed pseudofunctor is a pseudofunctor between functor
bicategories. Its identity and composition comparisons are pointwise those of the fixed
pseudofunctor, so this construction is generally not strict.

The common source bicategory is explicit because the fixed pseudofunctor `K`
determines the middle and target bicategories, but not that source. -/
def postcomp (K : Pseudofunctor B D) :
    Pseudofunctor
      (Pseudofunctor A B) (Pseudofunctor A D) where
  obj F := F.comp K
  map η := η.postcomp K
  map₂ Γ := StrongTrans.Hom.postcomp Γ K
  map₂_id η := StrongTrans.postcomp₂.id η K
  map₂_comp Γ Δ := StrongTrans.postcomp₂.comp Γ Δ K
  mapId := postcompMapId K
  mapComp := postcompMapComp K
  map₂_whisker_left := postcompMap₂_whisker_left K
  map₂_whisker_right := postcompMap₂_whisker_right K
  map₂_left_unitor := postcompMap₂_left_unitor K
  map₂_right_unitor := postcompMap₂_right_unitor K
  map₂_associator := postcompMap₂_associator K

/- Data and axiom audit (mathlib 4.32):

The object, `1`-morphism, `2`-morphism, identity, and composition data of
`postcomp` are concrete owners from the preceding layers. The private helpers
supply only `Prop`-valued naturality and bicategorical coherence fields. -/

end Postcomposition

end Pseudofunctor

end CategoryTheory
