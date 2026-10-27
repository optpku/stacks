/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Embedding.Connect
public import Mathlib.Algebra.Homology.Single
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.Sites.Grothendieck.AugmentationAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Augmentation Čech cochains of abelian sheaves

Stage direct images and restriction-induced transitions form a cosimplicial sheaf.
Its alternating-coface complex extends to an integer-indexed cochain with the
equalizer direct image in degree `-1`.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [IsFiberwiseSite F J]
variable [IsAugmentation F J K u0]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck AddCommGrpCat.{w})]

/-- Stage direct image `a_{n,*}` of abelian sheaves, i.e. cocontinuous sheaf
pushforward along the common composite `u_n`. -/
def IsAugmentation.abelianStagePushforward (n : SimplexCategory) :
    Sheaf (J (op n)).toGrothendieck AddCommGrpCat.{w} ⥤
      Sheaf K.toGrothendieck AddCommGrpCat.{w} :=
  (IsAugmentation.stageFunctor F u0 n).sheafPushforwardCocontinuous AddCommGrpCat.{w}
    (J (op n)).toGrothendieck K.toGrothendieck

/-- `abelianStagePushforward n` is cocontinuous sheaf pushforward along `u_n`. -/
theorem IsAugmentation.abelianStagePushforward_eq (n : SimplexCategory) :
    IsAugmentation.abelianStagePushforward F J K u0 n =
      (IsAugmentation.stageFunctor F u0 n).sheafPushforwardCocontinuous AddCommGrpCat.{w}
        (J (op n)).toGrothendieck K.toGrothendieck := sorry

/-- Adjunction `a_n⁻¹ ⊣ a_{n,*}` on abelian sheaves in the fiberwise case. -/
def IsAugmentation.abelianStagePushforward_adjunction (n : SimplexCategory) :
    IsAugmentation.abelianStageInverseImage F J K u0 n ⊣
      IsAugmentation.abelianStagePushforward F J K u0 n :=
  ((IsAugmentation.stageFunctor F u0 n).op.ranAdjunction AddCommGrpCat.{w} |>.comp
      (sheafificationAdjunction ((J (op n)).toGrothendieck) AddCommGrpCat.{w})).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf K.toGrothendieck AddCommGrpCat.{w})
    (Functor.FullyFaithful.id _) (Iso.refl _)
    ((IsAugmentation.stageFunctor F u0 n).sheafPushforwardCocontinuousCompSheafToPresheafIso
      AddCommGrpCat.{w} ((J (op n)).toGrothendieck) K.toGrothendieck).symm

/-- Direct-image mate of `a_m ∘ f_φ = a_n` on abelian sheaves in the fiberwise case. -/
def IsAugmentation.abelianStagePushforward_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (F.map φ.op).toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{w}
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck ⋙
      IsAugmentation.abelianStagePushforward F J K u0 m ≅
    IsAugmentation.abelianStagePushforward F J K u0 n :=
  Functor.sheafPushforwardCocontinuousComp'
    ((J (op n)).toGrothendieck) ((J (op m)).toGrothendieck) K.toGrothendieck
    (F.map φ.op).toFunctor (IsAugmentation.stageFunctor F u0 m)
    (IsAugmentation.stageFunctor_compIso F J K u0 φ)

/-- Restriction along a total-category simplex arrow is natural within its target stage. -/
private theorem fiberRestrictMapPresheaf_naturality (G : Sheaf (topology F J) AddCommGrpCat.{w})
    {m n : SimplexCategory} (φ : m ⟶ n)
    {V W : (F.obj (op n))ᵒᵖ} (η : V ⟶ W) :
    ((F.map φ.op).toFunctor.op ⋙
        ((fiberRestrict F J AddCommGrpCat.{w} m).obj G).obj).map η ≫
        G.obj.map (stageHom F φ W.unop).op =
      G.obj.map (stageHom F φ V.unop).op ≫
        ((fiberRestrict F J AddCommGrpCat.{w} n).obj G).obj.map η := sorry

/-- Presheaf-level transition `G_m ⟶ (f_φ)_* G_n`, the Ran mate of restriction along
`stageHom φ`. -/
def fiberRestrictMapPresheaf (G : Sheaf (topology F J) AddCommGrpCat.{w})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((fiberRestrict F J AddCommGrpCat.{w} m).obj G).obj ⟶
      (((F.map φ.op).toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{w}
          (J (op n)).toGrothendieck (J (op m)).toGrothendieck).obj
        ((fiberRestrict F J AddCommGrpCat.{w} n).obj G)).obj :=
  ((F.map φ.op).toFunctor.op.ranAdjunction AddCommGrpCat.{w}).homEquiv
      ((fiberRestrict F J AddCommGrpCat.{w} m).obj G).obj
      ((fiberRestrict F J AddCommGrpCat.{w} n).obj G).obj
    { app := fun V ↦ G.obj.map (stageHom F φ V.unop).op
      naturality := fun _ _ η ↦ fiberRestrictMapPresheaf_naturality F J G φ η }

/-- Restriction of `G` along the total-category arrow `(φ, 𝟙) : V ⟶ u_φ(V)`. -/
def fiberRestrictMap (G : Sheaf (topology F J) AddCommGrpCat.{w})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (fiberRestrict F J AddCommGrpCat.{w} m).obj G ⟶
      ((F.map φ.op).toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{w}
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck).obj
        ((fiberRestrict F J AddCommGrpCat.{w} n).obj G) :=
  ObjectProperty.homMk (fiberRestrictMapPresheaf F J G φ)

/-- The structure map `a_{m,*} G_m ⟶ a_{n,*} G_n` induced by a fiberwise simplex
operator `φ : m ⟶ n`. -/
def fiberAbelianStagePushforward_map (G : Sheaf (topology F J) AddCommGrpCat.{w})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (IsAugmentation.abelianStagePushforward F J K u0 m).obj
      ((fiberRestrict F J AddCommGrpCat.{w} m).obj G) ⟶
    (IsAugmentation.abelianStagePushforward F J K u0 n).obj
      ((fiberRestrict F J AddCommGrpCat.{w} n).obj G) :=
  (IsAugmentation.abelianStagePushforward F J K u0 m).map (fiberRestrictMap F J G φ) ≫
    (IsAugmentation.abelianStagePushforward_comp F J K u0 φ).hom.app
      ((fiberRestrict F J AddCommGrpCat.{w} n).obj G)

/-- The two maps `a_{0,*} G_0 ⇉ a_{1,*} G_1` induced by the coface operators `δ i`. -/
def fiberAbelianPushforwardParallel (G : Sheaf (topology F J) AddCommGrpCat.{w})
    (i : Fin 2) :
    (IsAugmentation.abelianStagePushforward F J K u0 ⦋0⦌).obj
      ((fiberRestrict F J AddCommGrpCat.{w} ⦋0⦌).obj G) ⟶
    (IsAugmentation.abelianStagePushforward F J K u0 ⦋1⦌).obj
      ((fiberRestrict F J AddCommGrpCat.{w} ⦋1⦌).obj G) :=
  fiberAbelianStagePushforward_map F J K u0 G (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)

/-- A morphism of total sheaves carries equalizing sections to equalizing sections. -/
private theorem IsAugmentation.abelianPushforwardMap_condition
    {A B : Sheaf (topology F J) AddCommGrpCat.{w}} (α : A ⟶ B) :
    (equalizer.ι (fiberAbelianPushforwardParallel F J K u0 A 0)
        (fiberAbelianPushforwardParallel F J K u0 A 1) ≫
      (IsAugmentation.abelianStagePushforward F J K u0 ⦋0⦌).map
        ((fiberRestrict F J AddCommGrpCat.{w} ⦋0⦌).map α)) ≫
        fiberAbelianPushforwardParallel F J K u0 B 0 =
      (equalizer.ι (fiberAbelianPushforwardParallel F J K u0 A 0)
        (fiberAbelianPushforwardParallel F J K u0 A 1) ≫
      (IsAugmentation.abelianStagePushforward F J K u0 ⦋0⦌).map
        ((fiberRestrict F J AddCommGrpCat.{w} ⦋0⦌).map α)) ≫
        fiberAbelianPushforwardParallel F J K u0 B 1 := sorry

/-- The equalizer morphism induced by a morphism of total sheaves. -/
private def IsAugmentation.abelianPushforwardMap
    {A B : Sheaf (topology F J) AddCommGrpCat.{w}} (α : A ⟶ B) :
    equalizer (fiberAbelianPushforwardParallel F J K u0 A 0)
      (fiberAbelianPushforwardParallel F J K u0 A 1) ⟶
      equalizer (fiberAbelianPushforwardParallel F J K u0 B 0)
        (fiberAbelianPushforwardParallel F J K u0 B 1) :=
  equalizer.lift (equalizer.ι (fiberAbelianPushforwardParallel F J K u0 A 0)
        (fiberAbelianPushforwardParallel F J K u0 A 1) ≫
      (IsAugmentation.abelianStagePushforward F J K u0 ⦋0⦌).map
        ((fiberRestrict F J AddCommGrpCat.{w} ⦋0⦌).map α))
    (IsAugmentation.abelianPushforwardMap_condition F J K u0 α)

/-- The induced equalizer morphisms preserve identities and composition. -/
private theorem IsAugmentation.abelianPushforwardMap_laws :
    (∀ A : Sheaf (topology F J) AddCommGrpCat.{w},
      IsAugmentation.abelianPushforwardMap F J K u0 (𝟙 A) =
        𝟙 (equalizer (fiberAbelianPushforwardParallel F J K u0 A 0)
          (fiberAbelianPushforwardParallel F J K u0 A 1))) ∧
    (∀ {A B E : Sheaf (topology F J) AddCommGrpCat.{w}} (α : A ⟶ B) (β : B ⟶ E),
      IsAugmentation.abelianPushforwardMap F J K u0 (α ≫ β) =
        IsAugmentation.abelianPushforwardMap F J K u0 α ≫
          IsAugmentation.abelianPushforwardMap F J K u0 β) := sorry

/-- Direct image `a_*` of abelian sheaves, sending `G` to the equalizer of
`a_{0,*} G_0 ⇉ a_{1,*} G_1`. -/
def IsAugmentation.abelianPushforward :
    Sheaf (topology F J) AddCommGrpCat.{w} ⥤
      Sheaf K.toGrothendieck AddCommGrpCat.{w} where
  obj G :=
    equalizer (fiberAbelianPushforwardParallel F J K u0 G 0)
      (fiberAbelianPushforwardParallel F J K u0 G 1)
  map α := IsAugmentation.abelianPushforwardMap F J K u0 α
  map_id A := (IsAugmentation.abelianPushforwardMap_laws F J K u0).1 A
  map_comp α β := (IsAugmentation.abelianPushforwardMap_laws F J K u0).2 α β

/-- The object `a_* G` is the equalizer of the two coface maps. -/
theorem IsAugmentation.abelianPushforward_obj
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    (IsAugmentation.abelianPushforward F J K u0).obj G =
      equalizer (fiberAbelianPushforwardParallel F J K u0 G 0)
        (fiberAbelianPushforwardParallel F J K u0 G 1) := sorry

/-- The comparison `a_* G ⟶ a_{0,*} G_0`. -/
def IsAugmentation.abelianPushforwardι
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    (IsAugmentation.abelianPushforward F J K u0).obj G ⟶
      (IsAugmentation.abelianStagePushforward F J K u0 ⦋0⦌).obj
        ((fiberRestrict F J AddCommGrpCat.{w} ⦋0⦌).obj G) :=
  equalizer.ι (fiberAbelianPushforwardParallel F J K u0 G 0)
    (fiberAbelianPushforwardParallel F J K u0 G 1)

/-- The simplex transition maps preserve identities and composition. -/
private theorem fiberPushforwardCosimplicial_laws (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    (∀ n : SimplexCategory,
      fiberAbelianStagePushforward_map F J K u0 G (𝟙 n) =
        𝟙 ((IsAugmentation.abelianStagePushforward F J K u0 n).obj
          ((fiberRestrict F J AddCommGrpCat.{w} n).obj G))) ∧
    (∀ {l m n : SimplexCategory} (φ : l ⟶ m) (ψ : m ⟶ n),
      fiberAbelianStagePushforward_map F J K u0 G (φ ≫ ψ) =
        fiberAbelianStagePushforward_map F J K u0 G φ ≫
          fiberAbelianStagePushforward_map F J K u0 G ψ) := sorry

/-- The cosimplicial abelian sheaf `n ↦ a_{n,*} G_n` on `D`. -/
def fiberPushforwardCosimplicial (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    CosimplicialObject (Sheaf K.toGrothendieck AddCommGrpCat.{w}) where
  obj n :=
    (IsAugmentation.abelianStagePushforward F J K u0 n).obj
      ((fiberRestrict F J AddCommGrpCat.{w} n).obj G)
  map φ := fiberAbelianStagePushforward_map F J K u0 G φ
  map_id n := (fiberPushforwardCosimplicial_laws F J K u0 G).1 n
  map_comp φ ψ := (fiberPushforwardCosimplicial_laws F J K u0 G).2 φ ψ

/-- Degree `n` of `fiberPushforwardCosimplicial` is the abelian sheaf `a_{n,*} G_n`. -/
theorem fiberPushforwardCosimplicial_obj (G : Sheaf (topology F J) AddCommGrpCat.{w})
    (n : SimplexCategory) :
    (fiberPushforwardCosimplicial F J K u0 G).obj n =
      (IsAugmentation.abelianStagePushforward F J K u0 n).obj
        ((fiberRestrict F J AddCommGrpCat.{w} n).obj G) := sorry

/-- The unaugmented cochain `a_{0,*} G_0 → a_{1,*} G_1 → ⋯` of abelian sheaves on
`D`. -/
abbrev fiberCechComplex (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    CochainComplex (Sheaf K.toGrothendieck AddCommGrpCat.{w}) ℕ :=
  (alternatingCofaceMapComplex _).obj (fiberPushforwardCosimplicial F J K u0 G)

/-- Degree `n` of `fiberCechComplex` is `a_{n,*} G_n`. -/
theorem fiberCechComplex_X (G : Sheaf (topology F J) AddCommGrpCat.{w}) (n : ℕ) :
    (fiberCechComplex F J K u0 G).X n =
      (fiberPushforwardCosimplicial F J K u0 G).obj ⦋n⦌ := sorry

/-- Differentials of `fiberCechComplex` are the alternating sums of coface maps. -/
theorem fiberCechComplex_d_eq (G : Sheaf (topology F J) AddCommGrpCat.{w}) (n : ℕ) :
    (fiberCechComplex F J K u0 G).d n (n + 1) =
      ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) • (fiberPushforwardCosimplicial F J K u0 G).δ i := sorry

/-- The connecting differential `a_* G ⟶ a_{0,*} G_0` from `single₀ (a_* G)` into
the unaugmented cochain. -/
def fiberCechConnect_d₀ (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    ((ChainComplex.single₀ _).obj
        ((IsAugmentation.abelianPushforward F J K u0).obj G)).X 0 ⟶
      (fiberCechComplex F J K u0 G).X 0 :=
  IsAugmentation.abelianPushforwardι F J K u0 G

/-- The connecting differential is the equalizer comparison `a_* G ⟶ a_{0,*} G_0`. -/
theorem fiberCechConnect_d₀_eq (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    fiberCechConnect_d₀ F J K u0 G = IsAugmentation.abelianPushforwardι F J K u0 G := sorry

/-- The connecting differential annihilates the outgoing differential of
`single₀ (a_* G)`. -/
theorem fiberCechConnect_comp_d₀ (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    ((ChainComplex.single₀ _).obj
          ((IsAugmentation.abelianPushforward F J K u0).obj G)).d 1 0 ≫
        fiberCechConnect_d₀ F J K u0 G = 0 := sorry

/-- The connecting differential equalizes the first coface of the unaugmented
cochain. -/
theorem fiberCechConnect_d₀_comp (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    fiberCechConnect_d₀ F J K u0 G ≫ (fiberCechComplex F J K u0 G).d 0 1 = 0 := sorry

/-- Connecting data for the ℤ-indexed cochain, with `a_* G` in degree `-1`. -/
def fiberCechConnect (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    CochainComplex.ConnectData
      ((ChainComplex.single₀ _).obj ((IsAugmentation.abelianPushforward F J K u0).obj G))
      (fiberCechComplex F J K u0 G) where
  d₀ := fiberCechConnect_d₀ F J K u0 G
  comp_d₀ := fiberCechConnect_comp_d₀ F J K u0 G
  d₀_comp := fiberCechConnect_d₀_comp F J K u0 G

/-- The canonical cochain `0 → a_* G → a_{0,*} G_0 → a_{1,*} G_1 → ⋯` of abelian
sheaves on `D`. -/
def fiberAugmentationCechCochain (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    CochainComplex (Sheaf K.toGrothendieck AddCommGrpCat.{w}) ℤ :=
  (fiberCechConnect F J K u0 G).cochainComplex

/-- Degree `-1` of `fiberAugmentationCechCochain` is the abelian sheaf `a_* G`. -/
theorem fiberAugmentationCechCochain_X_negOne
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    (fiberAugmentationCechCochain F J K u0 G).X (-1) =
      (IsAugmentation.abelianPushforward F J K u0).obj G := sorry

/-- Degree `n ≥ 0` of `fiberAugmentationCechCochain` is `a_{n,*} G_n`. -/
theorem fiberAugmentationCechCochain_X_ofNat
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) (n : ℕ) :
    (fiberAugmentationCechCochain F J K u0 G).X n =
      (IsAugmentation.abelianStagePushforward F J K u0 ⦋n⦌).obj
        ((fiberRestrict F J AddCommGrpCat.{w} ⦋n⦌).obj G) := sorry

/-- The differential out of degree `-1` is the comparison `a_* G ⟶ a_{0,*} G_0`. -/
theorem fiberAugmentationCechCochain_d_negOne_zero
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    (fiberAugmentationCechCochain F J K u0 G).d (-1) 0 =
      fiberCechConnect_d₀ F J K u0 G := sorry

/-- The augmented Čech cochain is exact in degrees `-1` and `0`. -/
theorem fiberAugmentationCechCochain_exactAt_negOne_zero
    (G : Sheaf (topology F J) AddCommGrpCat.{w})
    (n : ℤ) (hn : n = (-1 : ℤ) ∨ n = (0 : ℤ)) :
    (fiberAugmentationCechCochain F J K u0 G).ExactAt n := sorry

/-- The augmented Čech cochain of an injective total sheaf is acyclic. -/
theorem fiberAugmentationCechCochain_acyclic_of_injective
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) [Injective G] :
    (fiberAugmentationCechCochain F J K u0 G).Acyclic := sorry

end CategoryTheory.Grothendieck
