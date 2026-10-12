/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelian

/-!
# Abelian sheaf Hom and the free-abelian complex of a hypercovering

Internal Hom of abelian sheaves on a site, the free-abelian chain complex
`s(Z_{F(K)^#})` attached to a site-level hypercovering, and the cochain
complex `Hom(s(Z_{F(K)^#}), F)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{max w u v}]

/-- Whiskering a local morphism by `CategoryTheory.Over.map` is additive. -/
theorem abelianSheafHom_whisker_add (A B : Sheaf J AddCommGrpCat.{max w u v})
    {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (φ ψ : (CategoryTheory.Over.forget X.unop).op ⋙ A.obj ⟶ (CategoryTheory.Over.forget X.unop).op ⋙ B.obj) :
    Functor.whiskerLeft (CategoryTheory.Over.map f.unop).op (φ + ψ) =
      Functor.whiskerLeft (CategoryTheory.Over.map f.unop).op φ + Functor.whiskerLeft (CategoryTheory.Over.map f.unop).op ψ :=
  sorry

/-- Whiskering a local morphism by `CategoryTheory.Over.map` preserves zero. -/
theorem abelianSheafHom_whisker_zero (A B : Sheaf J AddCommGrpCat.{max w u v})
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Functor.whiskerLeft (CategoryTheory.Over.map f.unop).op
        (0 : (CategoryTheory.Over.forget X.unop).op ⋙ A.obj ⟶ (CategoryTheory.Over.forget X.unop).op ⋙ B.obj) = 0 :=
  sorry

/-- The additive restriction map on presheaf Hom over slices. -/
def abelianSheafHom_restrict (A B : Sheaf J AddCommGrpCat.{max w u v})
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((CategoryTheory.Over.forget X.unop).op ⋙ A.obj ⟶ (CategoryTheory.Over.forget X.unop).op ⋙ B.obj) →+
      ((CategoryTheory.Over.forget Y.unop).op ⋙ A.obj ⟶ (CategoryTheory.Over.forget Y.unop).op ⋙ B.obj) where
  toFun α := Functor.whiskerLeft (CategoryTheory.Over.map f.unop).op α
  map_zero' := abelianSheafHom_whisker_zero J A B f
  map_add' := abelianSheafHom_whisker_add J A B f

/-- The presheaf of abelian groups of local morphisms between abelian sheaves. -/
def abelianSheafHomPresheaf (A B : Sheaf J AddCommGrpCat.{max w u v}) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max w u v} where
  obj X :=
    AddCommGrpCat.of
      ((CategoryTheory.Over.forget X.unop).op ⋙ A.obj ⟶ (CategoryTheory.Over.forget X.unop).op ⋙ B.obj)
  map f := AddCommGrpCat.ofHom (abelianSheafHom_restrict J A B f)
  map_id := sorry
  map_comp := sorry

/-- The local-Hom presheaf of abelian sheaves satisfies the sheaf condition. -/
theorem abelianSheafHomPresheaf_isSheaf (A B : Sheaf J AddCommGrpCat.{max w u v}) :
    Presheaf.IsSheaf J (abelianSheafHomPresheaf J A B) :=
  sorry

/-- Internal Hom of abelian sheaves: the sheaf `Hom(A, B)` whose sections over `X`
are morphisms of restrictions to `C/X`. -/
def abelianSheafHom (A B : Sheaf J AddCommGrpCat.{max w u v}) :
    Sheaf J AddCommGrpCat.{max w u v} :=
  ⟨abelianSheafHomPresheaf J A B, abelianSheafHomPresheaf_isSheaf J A B⟩

/-- Sections of `abelianSheafHom A B` at `X` are morphisms of restrictions to `C/X`. -/
theorem abelianSheafHom_obj (A B : Sheaf J AddCommGrpCat.{max w u v}) (X : Cᵒᵖ) :
    (abelianSheafHom J A B).obj.obj X =
      AddCommGrpCat.of
        ((CategoryTheory.Over.forget X.unop).op ⋙ A.obj ⟶ (CategoryTheory.Over.forget X.unop).op ⋙ B.obj) :=
  sorry

variable [J.HasSheafCompose (forget AddCommGrpCat.{max w u v})]

/-- Componentwise equivalence between raw local Hom groups of `abelianSheafHom`
and sheaf morphisms on the over-site, which are the sections of `sheafHom`. -/
def abelianSheafHom_forget_equiv (A B : Sheaf J AddCommGrpCat.{max w u v}) (X : Cᵒᵖ) :
    ((sheafForget J).obj (abelianSheafHom J A B)).obj.obj X ≃
      (sheafHom A B).obj.obj X :=
  ((sheafHom'Iso A B).symm.app X).toEquiv

/-- Forgetting the abelian group structure on `abelianSheafHom A B` is canonically
isomorphic to the type-valued internal Hom sheaf. -/
def abelianSheafHom_forget (A B : Sheaf J AddCommGrpCat.{max w u v}) :
    (sheafForget J).obj (abelianSheafHom J A B) ≅ sheafHom A B :=
  (fullyFaithfulSheafToPresheaf J (Type (max w u v))).preimageIso (sheafHom'Iso A B).symm

/-- The component of `abelianSheafHom_forget` at `X` is `abelianSheafHom_forget_equiv`. -/
theorem abelianSheafHom_forget_hom_app
    (A B : Sheaf J AddCommGrpCat.{max w u v}) (X : Cᵒᵖ) :
    (abelianSheafHom_forget J A B).hom.hom.app X =
      (Equiv.toIso (abelianSheafHom_forget_equiv J A B X)).hom :=
  sorry

/-- Precomposition of local morphisms is additive. -/
theorem abelianSheafHom_precomp_add
    (A A' B : Sheaf J AddCommGrpCat.{max w u v}) (f : A' ⟶ A) (X : Cᵒᵖ)
    (φ ψ : (CategoryTheory.Over.forget X.unop).op ⋙ A.obj ⟶ (CategoryTheory.Over.forget X.unop).op ⋙ B.obj) :
    Functor.whiskerLeft (CategoryTheory.Over.forget X.unop).op f.hom ≫ (φ + ψ) =
      Functor.whiskerLeft (CategoryTheory.Over.forget X.unop).op f.hom ≫ φ +
        Functor.whiskerLeft (CategoryTheory.Over.forget X.unop).op f.hom ≫ ψ :=
  sorry

/-- Precomposition of local morphisms preserves zero. -/
theorem abelianSheafHom_precomp_zero
    (A A' B : Sheaf J AddCommGrpCat.{max w u v}) (f : A' ⟶ A) (X : Cᵒᵖ) :
    Functor.whiskerLeft (CategoryTheory.Over.forget X.unop).op f.hom ≫
        (0 : (CategoryTheory.Over.forget X.unop).op ⋙ A.obj ⟶ (CategoryTheory.Over.forget X.unop).op ⋙ B.obj) = 0 :=
  sorry

/-- The additive precomposition map on local Hom groups. -/
def abelianSheafHom_precomp
    (A A' B : Sheaf J AddCommGrpCat.{max w u v}) (f : A' ⟶ A) (X : Cᵒᵖ) :
    ((CategoryTheory.Over.forget X.unop).op ⋙ A.obj ⟶ (CategoryTheory.Over.forget X.unop).op ⋙ B.obj) →+
      ((CategoryTheory.Over.forget X.unop).op ⋙ A'.obj ⟶ (CategoryTheory.Over.forget X.unop).op ⋙ B.obj) where
  toFun φ := Functor.whiskerLeft (CategoryTheory.Over.forget X.unop).op f.hom ≫ φ
  map_zero' := abelianSheafHom_precomp_zero J A A' B f X
  map_add' := abelianSheafHom_precomp_add J A A' B f X

/-- Naturality of precomposition against restriction. -/
theorem abelianSheafHom_map_naturality
    (A A' B : Sheaf J AddCommGrpCat.{max w u v}) (f : A' ⟶ A) {X Y : Cᵒᵖ} (g : X ⟶ Y) :
    (abelianSheafHom J A B).obj.map g ≫
        AddCommGrpCat.ofHom (abelianSheafHom_precomp J A A' B f Y) =
      AddCommGrpCat.ofHom (abelianSheafHom_precomp J A A' B f X) ≫
        (abelianSheafHom J A' B).obj.map g :=
  sorry

/-- Precomposition `Hom(A, B) ⟶ Hom(A', B)` induced by `f : A' ⟶ A`. -/
def abelianSheafHom_map (A A' B : Sheaf J AddCommGrpCat.{max w u v}) (f : A' ⟶ A) :
    abelianSheafHom J A B ⟶ abelianSheafHom J A' B where
  hom :=
    { app := fun X ↦ AddCommGrpCat.ofHom (abelianSheafHom_precomp J A A' B f X)
      naturality := fun _ _ g ↦ abelianSheafHom_map_naturality J A A' B f g }

/-- `abelianSheafHom_map` of a zero morphism is zero. -/
theorem abelianSheafHom_map_zero (A A' B : Sheaf J AddCommGrpCat.{max w u v}) :
    abelianSheafHom_map J A A' B (0 : A' ⟶ A) = 0 :=
  sorry

/-- `abelianSheafHom_map` reverses composition. -/
theorem abelianSheafHom_map_comp (A A' A'' B : Sheaf J AddCommGrpCat.{max w u v})
    (f : A'' ⟶ A') (g : A' ⟶ A) :
    abelianSheafHom_map J A A'' B (f ≫ g) =
      abelianSheafHom_map J A A' B g ≫ abelianSheafHom_map J A' A'' B f :=
  sorry

variable [HasWeakSheafify J (Type (max w u v))]
variable (K : HypercoveringOf.Terminal.{w} J)

/-- Universe-aligned simplicial presheaf `F(K)` of a site-level hypercovering. -/
def hypercoveringPresheafULift :
    SimplicialObject (Cᵒᵖ ⥤ Type (max w u v)) :=
  hypercoveringPresheaf K.simplicial ⋙
    (Functor.whiskeringRight Cᵒᵖ (Type (max w v)) (Type (max w u v))).obj
      CategoryTheory.uliftFunctor.{u, max w v}

/-- The simplicial abelian sheaf obtained by freely abelianizing `F(K)` degreewise. -/
def freeAbelianSimplicial :
    SimplicialObject (Sheaf J AddCommGrpCat.{max w u v}) :=
  hypercoveringPresheafULift J K ⋙ J.freeAbelianSheafFunctor

/-- The free-abelian chain complex `s(Z_{F(K)^#})` of Definition 25.4.1, universe-aligned
so that Hom lands in `Ab(C)` at the same level as `a_n⁻¹ F`. -/
def freeAbelianComplex :
    ChainComplex (Sheaf J AddCommGrpCat.{max w u v}) ℕ :=
  (alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{max w u v})).obj
    (freeAbelianSimplicial J K)

/-- Degree `n` of `freeAbelianComplex` is the free abelian sheaf on the universe-lift of
`F(K_n)`. -/
theorem freeAbelianComplex_X (n : ℕ) :
    (freeAbelianComplex J K).X n =
      J.freeAbelianSheaf ((hypercoveringPresheafULift J K).obj (op ⦋n⦌)) :=
  sorry

/-- Shape axiom for the Hom cochain of `freeAbelianComplex`. -/
theorem homComplex_shape (F : Sheaf J AddCommGrpCat.{max w u v}) (i j : ℕ)
    (hij : ¬ (ComplexShape.up ℕ).Rel i j) :
    abelianSheafHom_map J ((freeAbelianComplex J K).X i) ((freeAbelianComplex J K).X j) F
        ((freeAbelianComplex J K).d j i) = 0 :=
  sorry

/-- Consecutive differentials of the Hom cochain compose to zero. -/
theorem homComplex_d_comp_d (F : Sheaf J AddCommGrpCat.{max w u v}) (i j k : ℕ) :
    abelianSheafHom_map J ((freeAbelianComplex J K).X i) ((freeAbelianComplex J K).X j) F
          ((freeAbelianComplex J K).d j i) ≫
        abelianSheafHom_map J ((freeAbelianComplex J K).X j) ((freeAbelianComplex J K).X k) F
          ((freeAbelianComplex J K).d k j) = 0 :=
  sorry

/-- The cochain complex `Hom(s(Z_{F(K)^#}), F)` of abelian sheaves. -/
def homComplex (F : Sheaf J AddCommGrpCat.{max w u v}) :
    CochainComplex (Sheaf J AddCommGrpCat.{max w u v}) ℕ where
  X n := abelianSheafHom J ((freeAbelianComplex J K).X n) F
  d i j :=
    abelianSheafHom_map J ((freeAbelianComplex J K).X i) ((freeAbelianComplex J K).X j) F
      ((freeAbelianComplex J K).d j i)
  shape i j hij := homComplex_shape J K F i j hij
  d_comp_d' i j k _ _ := homComplex_d_comp_d J K F i j k

/-- Degree `n` of `homComplex` is `abelianSheafHom` of the degree-`n` free abelian sheaf
into `F`. -/
theorem homComplex_X (F : Sheaf J AddCommGrpCat.{max w u v}) (n : ℕ) :
    (homComplex J K F).X n = abelianSheafHom J ((freeAbelianComplex J K).X n) F :=
  sorry

end CategoryTheory.SemiRepresentableFamily
