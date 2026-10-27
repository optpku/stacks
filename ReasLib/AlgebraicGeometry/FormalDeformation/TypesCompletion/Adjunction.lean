/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Truncation
public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion.Morphism
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Nilpotency

/-!
# Restriction and completion of set-valued functors

Restriction along the inclusion of Artinian local algebras is left adjoint to
completion by maximal-adic truncation limits. The counit is a natural isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open ArtinianLocalAlgCat CompleteLocalAlgCat

noncomputable section

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Restriction of Type-valued functors along `ArtinianLocalAlgCat.inclusion`. -/
def typesRestrictInclusion :
    (CompleteLocalAlgCat Λ k ⥤ Type w) ⥤ (ArtinianLocalAlgCat Λ k ⥤ Type w) :=
  (whiskeringLeft (ArtinianLocalAlgCat Λ k) (CompleteLocalAlgCat Λ k) (Type w)).obj
    ArtinianLocalAlgCat.inclusion

/-- Restriction of a Type-valued functor is precomposition with inclusion. -/
theorem typesRestrictInclusion_obj (G : CompleteLocalAlgCat Λ k ⥤ Type w) :
    typesRestrictInclusion.obj G = ArtinianLocalAlgCat.inclusion ⋙ G := rfl

/-- Restriction acts on natural transformations by left whiskering with inclusion. -/
theorem typesRestrictInclusion_map {G H : CompleteLocalAlgCat Λ k ⥤ Type w} (α : G ⟶ H) :
    typesRestrictInclusion.map α = whiskerLeft ArtinianLocalAlgCat.inclusion α := rfl

/-- The 1-functor sending a Type-valued functor on `C_Λ` to its set-valued completion
on `Ĉ_Λ`. -/
def typesCompletionFunctor :
    (ArtinianLocalAlgCat Λ k ⥤ Type w) ⥤ (CompleteLocalAlgCat Λ k ⥤ Type w) where
  obj := typesCompletion
  map := typesCompletionMap
  map_id := typesCompletionMap_id
  map_comp := typesCompletionMap_comp

/-- The object map of `typesCompletionFunctor` is set-valued completion. -/
theorem typesCompletionFunctor_obj (F : ArtinianLocalAlgCat Λ k ⥤ Type w) :
    typesCompletionFunctor.obj F = typesCompletion F := rfl

/-- The morphism map of `typesCompletionFunctor` is `typesCompletionMap`. -/
theorem typesCompletionFunctor_map {F G : ArtinianLocalAlgCat Λ k ⥤ Type w} (α : F ⟶ G) :
    typesCompletionFunctor.map α = typesCompletionMap α := rfl

private theorem typesCompletion_artinian_hom_ext {A B : ArtinianLocalAlgCat Λ k}
    {f g : A ⟶ B} (h : f.hom = g.hom) : f = g := by
  rcases f with ⟨f, hf, hf'⟩
  rcases g with ⟨g, hg, hg'⟩
  change f = g at h
  cases h
  rfl

private theorem typesCompletion_complete_hom_ext {S T : CompleteLocalAlgCat Λ k}
    {f g : S ⟶ T} (h : f.hom = g.hom) : f = g := by
  rcases f with ⟨f, hf, hf'⟩
  rcases g with ⟨g, hg, hg'⟩
  change f = g at h
  cases h
  rfl

private theorem typesCompletion_projection_comp (S : CompleteLocalAlgCat Λ k)
    {j j' : ℕᵒᵖ} (f : j ⟶ j') :
    truncationToInclusion S j.unop ≫ inclusion.map (S.truncationSystem.map f) =
      truncationToInclusion S j'.unop := by
  let π : (Functor.const ℕᵒᵖ).obj S ⟶ S.truncationSystem ⋙ inclusion :=
    NatTrans.ofOpSequence (truncationToInclusion S) (fun n ↦ by
      simp only [Functor.const_obj_map, Functor.comp_map,
        truncationSystem, ofOpSequence_map_homOfLE_succ]
      apply typesCompletion_complete_hom_ext
      apply AlgHom.ext
      intro x
      rfl)
  exact (π.naturality f).symm.trans (Category.id_comp _)

private theorem typesCompletion_projection_naturality {S T : CompleteLocalAlgCat Λ k}
    (f : S ⟶ T) (n : ℕ) :
    truncationToInclusion S n ≫ inclusion.map (truncationHom f n) =
      f ≫ truncationToInclusion T n := by
  apply typesCompletion_complete_hom_ext
  apply AlgHom.ext
  intro x
  rfl

private theorem typesCompletion_artinian_projection_comp (A : ArtinianLocalAlgCat Λ k)
    {j j' : ℕᵒᵖ} (f : j ⟶ j') :
    toTruncation A j.unop ≫ (inclusion.obj A).truncationSystem.map f =
      toTruncation A j'.unop := by
  apply typesCompletion_artinian_hom_ext
  exact congrArg CompleteLocalAlgCat.Hom.hom
    (typesCompletion_projection_comp (inclusion.obj A) f)

private theorem typesCompletion_nilpotency_projection (A : ArtinianLocalAlgCat Λ k) :
    toTruncation A (nilpotencyIndex A) ≫ (truncationNilpotencyIso A).hom = 𝟙 A := by
  letI := A.algebra
  apply typesCompletion_artinian_hom_ext
  apply AlgHom.ext
  intro x
  change truncationNilpotencyAlgEquiv A (Ideal.Quotient.mk _ x) = x
  rfl

private theorem typesCompletion_included_nilpotency_projection (A : ArtinianLocalAlgCat Λ k) :
    truncationToInclusion (inclusion.obj A) (nilpotencyIndex A) ≫
      inclusion.map (truncationNilpotencyIso A).hom = 𝟙 (inclusion.obj A) := by
  exact ((inclusion.map_comp _ _).symm.trans
    (congrArg inclusion.map (typesCompletion_nilpotency_projection A))).trans (inclusion.map_id A)

/-- Images of a point under the quotient maps form a compatible truncation tower. -/
theorem typesCompletionUnit_compatible (G : CompleteLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) (x : G.obj S) :
    ∀ (j j' : ℕᵒᵖ) (f : j ⟶ j'),
      (S.truncationSystem ⋙ typesRestrictInclusion.obj G).map f
          (G.map (truncationToInclusion S j.unop) x) =
        G.map (truncationToInclusion S j'.unop) x := by
  intro j j' f
  change G.map (inclusion.map (S.truncationSystem.map f))
    (G.map (truncationToInclusion S j.unop) x) = _
  calc
    _ = G.map (truncationToInclusion S j.unop ≫
        inclusion.map (S.truncationSystem.map f)) x := (G.map_comp_apply _ _ x).symm
    _ = _ := congrArg (fun h ↦ G.map h x) (typesCompletion_projection_comp S f)

/-- The quotient-image tower is natural in the complete local algebra. -/
theorem typesCompletionUnit_app_naturality (G : CompleteLocalAlgCat Λ k ⥤ Type w)
    {S T : CompleteLocalAlgCat Λ k} (f : S ⟶ T) :
    G.map f ≫ TypeCat.ofHom (fun x ↦
      Types.Limit.mk (T.truncationSystem ⋙ typesRestrictInclusion.obj G)
        (fun j ↦ G.map (truncationToInclusion T j.unop) x)
        (typesCompletionUnit_compatible G T x)) =
      TypeCat.ofHom (fun x ↦
      Types.Limit.mk (S.truncationSystem ⋙ typesRestrictInclusion.obj G)
        (fun j ↦ G.map (truncationToInclusion S j.unop) x)
        (typesCompletionUnit_compatible G S x)) ≫
        (typesCompletion (typesRestrictInclusion.obj G)).map f := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Types.limit_ext
  intro j
  simp only [types_comp_apply, TypeCat.ofHom_apply, typesCompletion,
    limMap_π_apply, Types.Limit.π_mk, whiskerRight_app,
    truncationSystemMap, NatTrans.ofOpSequence_app]
  change G.map (truncationToInclusion T j.unop) (G.map f x) =
    G.map (inclusion.map (truncationHom f j.unop))
      (G.map (truncationToInclusion S j.unop) x)
  rw [← types_comp_apply, ← types_comp_apply, ← G.map_comp, ← G.map_comp,
    typesCompletion_projection_naturality]

/-- The quotient-image tower is natural in the set-valued functor. -/
theorem typesCompletionUnit_naturality {G H : CompleteLocalAlgCat Λ k ⥤ Type w}
    (α : G ⟶ H) (S : CompleteLocalAlgCat Λ k) :
    α.app S ≫ TypeCat.ofHom (fun x ↦
      Types.Limit.mk (S.truncationSystem ⋙ typesRestrictInclusion.obj H)
        (fun j ↦ H.map (truncationToInclusion S j.unop) x)
        (typesCompletionUnit_compatible H S x)) =
      TypeCat.ofHom (fun x ↦
      Types.Limit.mk (S.truncationSystem ⋙ typesRestrictInclusion.obj G)
        (fun j ↦ G.map (truncationToInclusion S j.unop) x)
        (typesCompletionUnit_compatible G S x)) ≫
        (typesCompletionMap (typesRestrictInclusion.map α)).app S := by
  apply ConcreteCategory.hom_ext
  intro x
  change Types.Limit.mk (S.truncationSystem ⋙ typesRestrictInclusion.obj H)
      (fun j ↦ H.map (truncationToInclusion S j.unop) (α.app S x))
      (typesCompletionUnit_compatible H S (α.app S x)) =
    limMap (whiskerLeft S.truncationSystem (typesRestrictInclusion.map α))
      (Types.Limit.mk (S.truncationSystem ⋙ typesRestrictInclusion.obj G)
        (fun j ↦ G.map (truncationToInclusion S j.unop) x)
        (typesCompletionUnit_compatible G S x))
  apply Types.limit_ext
  intro j
  simp only [limMap_π_apply, Types.Limit.π_mk, whiskerLeft_app]
  exact (ConcreteCategory.congr_hom (α.naturality (truncationToInclusion S j.unop)) x).symm

/-- The unit sends a point to the tower of its images under the truncation projections. -/
def typesCompletionUnit :
    𝟭 (CompleteLocalAlgCat Λ k ⥤ Type w) ⟶
      typesRestrictInclusion ⋙ typesCompletionFunctor where
  app G :=
    { app S := TypeCat.ofHom fun x ↦
        Types.Limit.mk (S.truncationSystem ⋙ typesRestrictInclusion.obj G)
          (fun j ↦ G.map (truncationToInclusion S j.unop) x)
          (typesCompletionUnit_compatible G S x)
      naturality {_ _} f := typesCompletionUnit_app_naturality G f }
  naturality {_ _} α := by
    apply NatTrans.ext
    funext S
    exact typesCompletionUnit_naturality α S

/-- The unit tower at stage `n` is the image under the truncation projection. -/
theorem typesCompletionUnit_app (G : CompleteLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) (x : G.obj S) (n : ℕ) :
    limit.π (S.truncationSystem ⋙ typesRestrictInclusion.obj G) (op n)
        ((typesCompletionUnit.app G).app S x) =
      G.map (truncationToInclusion S n) x :=
  Types.Limit.π_mk _ _ _ _

private theorem typesCompletion_artinian_projection_naturality
    {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) (n : ℕ) :
    toTruncation A n ≫ truncationHom (inclusion.map f) n = f ≫ toTruncation B n := by
  apply typesCompletion_artinian_hom_ext
  exact congrArg CompleteLocalAlgCat.Hom.hom
    (typesCompletion_projection_naturality (inclusion.map f) n)

/-- Evaluation at a nilpotent stage recovers every projection of the truncation limit. -/
private theorem typesCompletion_evaluation_π (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (A : ArtinianLocalAlgCat Λ k) (j : ℕᵒᵖ) :
    (limit.π ((inclusion.obj A).truncationSystem ⋙ F) (op (nilpotencyIndex A)) ≫
      F.map (truncationNilpotencyIso A).hom) ≫ F.map (toTruncation A j.unop) =
        limit.π ((inclusion.obj A).truncationSystem ⋙ F) j := by
  let m := max (nilpotencyIndex A) j.unop
  let a : op m ⟶ op (nilpotencyIndex A) := (homOfLE (Nat.le_max_left _ _)).op
  let b : op m ⟶ j := (homOfLE (Nat.le_max_right _ _)).op
  have h : (inclusion.obj A).truncationSystem.map a ≫
      (truncationNilpotencyIso A).hom ≫ toTruncation A j.unop =
        (inclusion.obj A).truncationSystem.map b := by
    apply typesCompletion_artinian_hom_ext
    apply DFunLike.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : ((inclusion.obj A).truncationSystem.map a).hom ((toTruncation A m).hom y) =
        (toTruncation A (nilpotencyIndex A)).hom y :=
      congrArg (fun f ↦ f.hom y) (typesCompletion_artinian_projection_comp A a)
    have hb : ((inclusion.obj A).truncationSystem.map b).hom ((toTruncation A m).hom y) =
        (toTruncation A j.unop).hom y :=
      congrArg (fun f ↦ f.hom y) (typesCompletion_artinian_projection_comp A b)
    change (toTruncation A j.unop).hom ((truncationNilpotencyIso A).hom.hom
      (((inclusion.obj A).truncationSystem.map a).hom ((toTruncation A m).hom y))) =
        ((inclusion.obj A).truncationSystem.map b).hom ((toTruncation A m).hom y)
    rw [ha, hb]
    rfl
  let D := (inclusion.obj A).truncationSystem ⋙ F
  apply ConcreteCategory.hom_ext
  intro x
  change F.map (toTruncation A j.unop) (F.map (truncationNilpotencyIso A).hom
    (limit.π D (op (nilpotencyIndex A)) x)) = limit.π D j x
  have hx : F.map ((inclusion.obj A).truncationSystem.map a) (limit.π D (op m) x) =
      limit.π D (op (nilpotencyIndex A)) x :=
    ConcreteCategory.congr_hom (limit.w D a) x
  have hp : F.map (toTruncation A j.unop) (F.map (truncationNilpotencyIso A).hom
      (limit.π D (op (nilpotencyIndex A)) x)) =
        F.map ((inclusion.obj A).truncationSystem.map b) (limit.π D (op m) x) := by
    calc
      _ = F.map (toTruncation A j.unop) (F.map (truncationNilpotencyIso A).hom
          (F.map ((inclusion.obj A).truncationSystem.map a) (limit.π D (op m) x))) :=
        congrArg (fun y ↦ F.map (toTruncation A j.unop)
          (F.map (truncationNilpotencyIso A).hom y)) hx.symm
      _ = F.map ((inclusion.obj A).truncationSystem.map a ≫
          (truncationNilpotencyIso A).hom ≫ toTruncation A j.unop) (limit.π D (op m) x) :=
        ((F.map_comp_apply ((inclusion.obj A).truncationSystem.map a)
          ((truncationNilpotencyIso A).hom ≫ toTruncation A j.unop) (limit.π D (op m) x)).trans
            (F.map_comp_apply (truncationNilpotencyIso A).hom (toTruncation A j.unop)
              (F.map ((inclusion.obj A).truncationSystem.map a) (limit.π D (op m) x)))).symm
      _ = F.map ((inclusion.obj A).truncationSystem.map b) (limit.π D (op m) x) :=
        congrArg (fun f ↦ F.map f (limit.π D (op m) x)) h
  exact hp.trans (ConcreteCategory.congr_hom (limit.w D b) x)

/-- Nilpotency-stage evaluation is natural in the Artinian local algebra. -/
theorem typesCompletionCounit_app_naturality (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    (typesRestrictInclusion.obj (typesCompletion F)).map f ≫ (limit.π ((inclusion.obj B).truncationSystem ⋙ F)
      (op (nilpotencyIndex B)) ≫ F.map (truncationNilpotencyIso B).hom) =
      (limit.π ((inclusion.obj A).truncationSystem ⋙ F)
      (op (nilpotencyIndex A)) ≫ F.map (truncationNilpotencyIso A).hom) ≫ F.map f := by
  let n := nilpotencyIndex B
  have h : toTruncation A n ≫ truncationHom (inclusion.map f) n ≫
      (truncationNilpotencyIso B).hom = f := by
    erw [← Category.assoc, typesCompletion_artinian_projection_naturality,
      Category.assoc, typesCompletion_nilpotency_projection, Category.comp_id]
  change limMap (whiskerRight (truncationSystemMap (inclusion.map f)) F) ≫
    (limit.π ((inclusion.obj B).truncationSystem ⋙ F) (op n) ≫
      F.map (truncationNilpotencyIso B).hom) = _
  calc
    _ = limit.π ((inclusion.obj A).truncationSystem ⋙ F) (op n) ≫
        F.map (truncationHom (inclusion.map f) n) ≫
          F.map (truncationNilpotencyIso B).hom := by
      rw [← Category.assoc, limMap_π, Category.assoc]
      rfl
    _ = (limit.π ((inclusion.obj A).truncationSystem ⋙ F) (op (nilpotencyIndex A)) ≫
        F.map (truncationNilpotencyIso A).hom) ≫ F.map f := by
      rw [← typesCompletion_evaluation_π F A (op n)]
      erw [Category.assoc, Category.assoc, ← F.map_comp, ← F.map_comp, h]
      rfl

/-- Nilpotency-stage evaluation is natural in the set-valued functor. -/
theorem typesCompletionCounit_naturality {F H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (α : F ⟶ H) (A : ArtinianLocalAlgCat Λ k) :
    (typesRestrictInclusion.map (typesCompletionMap α)).app A ≫ (limit.π ((inclusion.obj A).truncationSystem ⋙ H)
      (op (nilpotencyIndex A)) ≫ H.map (truncationNilpotencyIso A).hom) =
      (limit.π ((inclusion.obj A).truncationSystem ⋙ F)
      (op (nilpotencyIndex A)) ≫ F.map (truncationNilpotencyIso A).hom) ≫ α.app A := by
  change limMap (whiskerLeft (inclusion.obj A).truncationSystem α) ≫
      (limit.π ((inclusion.obj A).truncationSystem ⋙ H) (op (nilpotencyIndex A)) ≫
        H.map (truncationNilpotencyIso A).hom) =
    (limit.π ((inclusion.obj A).truncationSystem ⋙ F) (op (nilpotencyIndex A)) ≫
      F.map (truncationNilpotencyIso A).hom) ≫ α.app A
  calc
    _ = limit.π ((inclusion.obj A).truncationSystem ⋙ F) (op (nilpotencyIndex A)) ≫
        α.app ((toComplete A).truncation (nilpotencyIndex A)) ≫
          H.map (truncationNilpotencyIso A).hom := by
      rw [← Category.assoc, limMap_π]
      rfl
    _ = _ := by
      exact (congrArg (fun h ↦ limit.π ((inclusion.obj A).truncationSystem ⋙ F)
        (op (nilpotencyIndex A)) ≫ h) (α.naturality (truncationNilpotencyIso A).hom).symm).trans
          (Category.assoc _ _ _).symm

/-- The counit evaluates the limit at the nilpotency stage and applies the quotient
identification with the Artinian local algebra. -/
def typesCompletionCounit :
    typesCompletionFunctor ⋙ typesRestrictInclusion ⟶
      𝟭 (ArtinianLocalAlgCat Λ k ⥤ Type w) where
  app F :=
    { app A :=
        limit.π ((inclusion.obj A).truncationSystem ⋙ F) (op (nilpotencyIndex A)) ≫
          F.map (truncationNilpotencyIso A).hom
      naturality {_ _} f := typesCompletionCounit_app_naturality F f }
  naturality {_ _} α := by
    apply NatTrans.ext
    funext A
    exact typesCompletionCounit_naturality α A

/-- The counit is the nilpotency-stage projection followed by the nilpotency identification. -/
theorem typesCompletionCounit_app (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (A : ArtinianLocalAlgCat Λ k) :
    (typesCompletionCounit.app F).app A =
      limit.π ((inclusion.obj A).truncationSystem ⋙ F) (op (nilpotencyIndex A)) ≫
        F.map (truncationNilpotencyIso A).hom := rfl

/-- Restriction of the unit followed by the counit is the identity. -/
theorem typesCompletion_left_triangle (G : CompleteLocalAlgCat Λ k ⥤ Type w) :
    typesRestrictInclusion.map (typesCompletionUnit.app G) ≫
        typesCompletionCounit.app (typesRestrictInclusion.obj G) =
      𝟙 (typesRestrictInclusion.obj G) := by
  apply NatTrans.ext
  funext A
  apply ConcreteCategory.hom_ext
  intro x
  change G.map (inclusion.map (truncationNilpotencyIso A).hom)
    (limit.π ((inclusion.obj A).truncationSystem ⋙ typesRestrictInclusion.obj G)
      (op (nilpotencyIndex A)) ((typesCompletionUnit.app G).app (inclusion.obj A) x)) = x
  rw [typesCompletionUnit_app]
  calc
    _ = G.map (truncationToInclusion (inclusion.obj A) (nilpotencyIndex A) ≫
        inclusion.map (truncationNilpotencyIso A).hom) x := (G.map_comp_apply _ _ x).symm
    _ = x := by
      rw [typesCompletion_included_nilpotency_projection, G.map_id]
      rfl

/-- Projecting to an Artinian truncation and evaluating its completion gives the original
limit projection. -/
private theorem typesCompletion_truncation_evaluation
    (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (S : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (typesCompletion F).map (truncationToInclusion S n) ≫
      (limit.π ((inclusion.obj (S.truncation n)).truncationSystem ⋙ F)
        (op (nilpotencyIndex (S.truncation n))) ≫
          F.map (truncationNilpotencyIso (S.truncation n)).hom) =
      limit.π (S.truncationSystem ⋙ F) (op n) := by
  let A := S.truncation n
  let m := nilpotencyIndex A
  let M := max m n
  let a : op M ⟶ op m := (homOfLE (Nat.le_max_left _ _)).op
  let b : op M ⟶ op n := (homOfLE (Nat.le_max_right _ _)).op
  have h : S.truncationSystem.map a ≫ truncationHom (truncationToInclusion S n) m ≫
      (truncationNilpotencyIso A).hom = S.truncationSystem.map b := by
    apply typesCompletion_artinian_hom_ext
    apply DFunLike.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : (S.truncationSystem.map a).hom ((truncationToInclusion S M).hom y) =
        (truncationToInclusion S m).hom y :=
      congrArg (fun f ↦ f.hom y) (typesCompletion_projection_comp S a)
    have hb : (S.truncationSystem.map b).hom ((truncationToInclusion S M).hom y) =
        (truncationToInclusion S n).hom y :=
      congrArg (fun f ↦ f.hom y) (typesCompletion_projection_comp S b)
    change (truncationNilpotencyIso A).hom.hom
      ((truncationHom (truncationToInclusion S n) m).hom
        ((S.truncationSystem.map a).hom ((truncationToInclusion S M).hom y))) =
          (S.truncationSystem.map b).hom ((truncationToInclusion S M).hom y)
    rw [ha, hb]
    rfl
  let D := S.truncationSystem ⋙ F
  apply ConcreteCategory.hom_ext
  intro x
  change F.map (truncationNilpotencyIso A).hom
    (limit.π ((inclusion.obj A).truncationSystem ⋙ F) (op m)
      ((typesCompletion F).map (truncationToInclusion S n) x)) = limit.π D (op n) x
  have hm : limit.π ((inclusion.obj A).truncationSystem ⋙ F) (op m)
      ((typesCompletion F).map (truncationToInclusion S n) x) =
        F.map (truncationHom (truncationToInclusion S n) m) (limit.π D (op m) x) :=
    limMap_π_apply (whiskerRight (truncationSystemMap (truncationToInclusion S n)) F) (op m) x
  have hx : F.map (S.truncationSystem.map a) (limit.π D (op M) x) =
      limit.π D (op m) x := ConcreteCategory.congr_hom (limit.w D a) x
  have hp : F.map (truncationNilpotencyIso A).hom
      (limit.π ((inclusion.obj A).truncationSystem ⋙ F) (op m)
        ((typesCompletion F).map (truncationToInclusion S n) x)) =
          F.map (S.truncationSystem.map b) (limit.π D (op M) x) := by
    calc
      _ = F.map (truncationNilpotencyIso A).hom
          (F.map (truncationHom (truncationToInclusion S n) m) (limit.π D (op m) x)) :=
        congrArg (F.map (truncationNilpotencyIso A).hom) hm
      _ = F.map (truncationNilpotencyIso A).hom
          (F.map (truncationHom (truncationToInclusion S n) m)
            (F.map (S.truncationSystem.map a) (limit.π D (op M) x))) :=
        congrArg (fun y ↦ F.map (truncationNilpotencyIso A).hom
          (F.map (truncationHom (truncationToInclusion S n) m) y)) hx.symm
      _ = F.map (S.truncationSystem.map a ≫ truncationHom (truncationToInclusion S n) m ≫
          (truncationNilpotencyIso A).hom) (limit.π D (op M) x) :=
        ((F.map_comp_apply (S.truncationSystem.map a)
          (truncationHom (truncationToInclusion S n) m ≫ (truncationNilpotencyIso A).hom)
          (limit.π D (op M) x)).trans
            (F.map_comp_apply (truncationHom (truncationToInclusion S n) m)
              (truncationNilpotencyIso A).hom
              (F.map (S.truncationSystem.map a) (limit.π D (op M) x)))).symm
      _ = F.map (S.truncationSystem.map b) (limit.π D (op M) x) :=
        congrArg (fun f ↦ F.map f (limit.π D (op M) x)) h
  exact hp.trans (ConcreteCategory.congr_hom (limit.w D b) x)

/-- The unit of a completed functor followed by completion of the counit is the identity. -/
theorem typesCompletion_right_triangle (F : ArtinianLocalAlgCat Λ k ⥤ Type w) :
    typesCompletionUnit.app (typesCompletionFunctor.obj F) ≫
        typesCompletionFunctor.map (typesCompletionCounit.app F) =
      𝟙 (typesCompletionFunctor.obj F) := by
  apply NatTrans.ext
  funext S
  apply limit.hom_ext
  intro j
  let c : typesRestrictInclusion.obj (typesCompletion F) ⟶ F := typesCompletionCounit.app F
  change ((typesCompletionUnit.app (typesCompletion F)).app S ≫
    limMap (whiskerLeft S.truncationSystem c)) ≫
      limit.π (S.truncationSystem ⋙ F) j = 𝟙 _ ≫ limit.π (S.truncationSystem ⋙ F) j
  erw [Category.assoc, limMap_π (whiskerLeft S.truncationSystem c) j, Category.id_comp]
  have hunit : (typesCompletionUnit.app (typesCompletion F)).app S ≫
      limit.π (S.truncationSystem ⋙ typesRestrictInclusion.obj (typesCompletion F)) j =
        (typesCompletion F).map (truncationToInclusion S j.unop) := by
    apply ConcreteCategory.hom_ext
    intro x
    exact typesCompletionUnit_app (typesCompletion F) S x j.unop
  erw [← Category.assoc, hunit]
  exact typesCompletion_truncation_evaluation F S j.unop

/-- Restriction along inclusion is left adjoint to set-valued completion. -/
def typesCompletionAdjunction :
    (typesRestrictInclusion :
        (CompleteLocalAlgCat Λ k ⥤ Type w) ⥤
          (ArtinianLocalAlgCat Λ k ⥤ Type w)) ⊣
      (typesCompletionFunctor :
        (ArtinianLocalAlgCat Λ k ⥤ Type w) ⥤
          (CompleteLocalAlgCat Λ k ⥤ Type w)) where
  unit := typesCompletionUnit
  counit := typesCompletionCounit
  left_triangle_components := typesCompletion_left_triangle
  right_triangle_components := typesCompletion_right_triangle

/-- The unit of `typesCompletionAdjunction` is `typesCompletionUnit`. -/
theorem typesCompletionAdjunction_unit :
    typesCompletionAdjunction.unit =
      (typesCompletionUnit :
        𝟭 (CompleteLocalAlgCat Λ k ⥤ Type w) ⟶
          typesRestrictInclusion ⋙ typesCompletionFunctor) := rfl

/-- The counit of `typesCompletionAdjunction` is `typesCompletionCounit`. -/
theorem typesCompletionAdjunction_counit :
    typesCompletionAdjunction.counit =
      (typesCompletionCounit :
        typesCompletionFunctor ⋙ typesRestrictInclusion ⟶
          𝟭 (ArtinianLocalAlgCat Λ k ⥤ Type w)) := rfl

/-- Restriction along inclusion is a left adjoint. -/
instance typesRestrictInclusion.isLeftAdjoint :
    IsLeftAdjoint
      (typesRestrictInclusion :
        (CompleteLocalAlgCat Λ k ⥤ Type w) ⥤
          (ArtinianLocalAlgCat Λ k ⥤ Type w)) where
  exists_rightAdjoint := ⟨typesCompletionFunctor, ⟨typesCompletionAdjunction⟩⟩

/-- Set-valued completion is a right adjoint. -/
instance typesCompletionFunctor.isRightAdjoint :
    IsRightAdjoint
      (typesCompletionFunctor :
        (ArtinianLocalAlgCat Λ k ⥤ Type w) ⥤
          (CompleteLocalAlgCat Λ k ⥤ Type w)) where
  exists_leftAdjoint := ⟨typesRestrictInclusion, ⟨typesCompletionAdjunction⟩⟩

/-- The natural hom equivalence between restriction and completion, given by the unit
and counit of their adjunction. -/
def typesCompletionHomEquiv (G : CompleteLocalAlgCat Λ k ⥤ Type w)
    (F : ArtinianLocalAlgCat Λ k ⥤ Type w) :
    (typesRestrictInclusion.obj G ⟶ F) ≃ (G ⟶ typesCompletionFunctor.obj F) :=
  typesCompletionAdjunction.homEquiv G F

/-- `typesCompletionHomEquiv` sends `α` to the unit followed by completion of `α`. -/
theorem typesCompletionHomEquiv_apply (G : CompleteLocalAlgCat Λ k ⥤ Type w)
    (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (α : typesRestrictInclusion.obj G ⟶ F) :
    typesCompletionHomEquiv G F α =
      typesCompletionUnit.app G ≫ typesCompletionFunctor.map α := rfl

/-- The inverse of `typesCompletionHomEquiv` sends `ψ` to the restriction of `ψ`
followed by the counit. -/
theorem typesCompletionHomEquiv_symm_apply (G : CompleteLocalAlgCat Λ k ⥤ Type w)
    (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (ψ : G ⟶ typesCompletionFunctor.obj F) :
    (typesCompletionHomEquiv G F).symm ψ =
      typesRestrictInclusion.map ψ ≫ typesCompletionCounit.app F := rfl

/-- Images of a point under the Artinian quotient maps form a compatible tower. -/
theorem typesCompletionCounitIsoApp_compatible (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (A : ArtinianLocalAlgCat Λ k) (x : F.obj A) :
    ∀ (j j' : ℕᵒᵖ) (f : j ⟶ j'),
      ((inclusion.obj A).truncationSystem ⋙ F).map f
          (F.map (toTruncation A j.unop) x) =
        F.map (toTruncation A j'.unop) x := by
  intro j j' f
  change F.map ((inclusion.obj A).truncationSystem.map f)
    (F.map (toTruncation A j.unop) x) = _
  calc
    _ = F.map (toTruncation A j.unop ≫ (inclusion.obj A).truncationSystem.map f) x :=
      (F.map_comp_apply _ _ x).symm
    _ = _ := congrArg (fun h ↦ F.map h x) (typesCompletion_artinian_projection_comp A f)

/-- Evaluation followed by the quotient-image tower is the identity on completion. -/
theorem typesCompletionCounitIsoApp_hom_inv_id
    (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (A : ArtinianLocalAlgCat Λ k) :
    (typesCompletionCounit.app F).app A ≫ TypeCat.ofHom (fun x ↦
      Types.Limit.mk ((inclusion.obj A).truncationSystem ⋙ F)
        (fun j ↦ F.map (toTruncation A j.unop) x)
        (typesCompletionCounitIsoApp_compatible F A x)) =
      𝟙 ((typesCompletion F).obj (inclusion.obj A)) := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Types.limit_ext
  intro j
  change limit.π ((inclusion.obj A).truncationSystem ⋙ F) j
    (Types.Limit.mk _ _ _) = limit.π ((inclusion.obj A).truncationSystem ⋙ F) j x
  rw [Types.Limit.π_mk]
  exact ConcreteCategory.congr_hom (typesCompletion_evaluation_π F A j) x

/-- The quotient-image tower followed by evaluation is the identity on the original set. -/
theorem typesCompletionCounitIsoApp_inv_hom_id
    (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (A : ArtinianLocalAlgCat Λ k) :
    TypeCat.ofHom (fun x ↦
      Types.Limit.mk ((inclusion.obj A).truncationSystem ⋙ F)
        (fun j ↦ F.map (toTruncation A j.unop) x)
        (typesCompletionCounitIsoApp_compatible F A x)) ≫ (typesCompletionCounit.app F).app A = 𝟙 (F.obj A) := by
  apply ConcreteCategory.hom_ext
  intro x
  change F.map (truncationNilpotencyIso A).hom
    (limit.π ((inclusion.obj A).truncationSystem ⋙ F) (op (nilpotencyIndex A))
      (Types.Limit.mk ((inclusion.obj A).truncationSystem ⋙ F)
        (fun j ↦ F.map (toTruncation A j.unop) x)
        (typesCompletionCounitIsoApp_compatible F A x))) = x
  rw [Types.Limit.π_mk, ← types_comp_apply, ← F.map_comp,
    typesCompletion_nilpotency_projection, F.map_id]
  rfl

/-- The counit isomorphism at an Artinian local algebra, with inverse the quotient-image tower. -/
def typesCompletionCounitIsoApp (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (A : ArtinianLocalAlgCat Λ k) :
    (typesCompletion F).obj (inclusion.obj A) ≅ F.obj A where
  hom := (typesCompletionCounit.app F).app A
  inv := TypeCat.ofHom fun x ↦
    Types.Limit.mk ((inclusion.obj A).truncationSystem ⋙ F)
      (fun j ↦ F.map (toTruncation A j.unop) x)
      (typesCompletionCounitIsoApp_compatible F A x)
  hom_inv_id := typesCompletionCounitIsoApp_hom_inv_id F A
  inv_hom_id := typesCompletionCounitIsoApp_inv_hom_id F A

/-- The hom of `typesCompletionCounitIsoApp` is the counit component. -/
theorem typesCompletionCounitIsoApp_hom (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (A : ArtinianLocalAlgCat Λ k) :
    (typesCompletionCounitIsoApp F A).hom = (typesCompletionCounit.app F).app A := rfl

/-- The inverse of `typesCompletionCounitIsoApp` projects at stage `n` to
`F.map (toTruncation A n)`. -/
theorem typesCompletionCounitIsoApp_inv (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (A : ArtinianLocalAlgCat Λ k) (x : F.obj A) (n : ℕ) :
    limit.π ((inclusion.obj A).truncationSystem ⋙ F) (op n)
        ((typesCompletionCounitIsoApp F A).inv x) =
      F.map (toTruncation A n) x :=
  Types.Limit.π_mk _ _ _ _

/-- The counit `hat F |_{C_Λ} ⟶ F` is a natural isomorphism. -/
def typesCompletionCounitIso :
    typesCompletionFunctor ⋙ typesRestrictInclusion ≅
      𝟭 (ArtinianLocalAlgCat Λ k ⥤ Type w) :=
  NatIso.ofComponents
    (fun F ↦ NatIso.ofComponents (fun A ↦ typesCompletionCounitIsoApp F A)
      (fun f ↦ (typesCompletionCounit.app F).naturality f))
    (fun α ↦ typesCompletionCounit.naturality α)

/-- The hom of `typesCompletionCounitIso` at `F` and `A` is the counit component. -/
theorem typesCompletionCounitIso_hom_app (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (A : ArtinianLocalAlgCat Λ k) :
    (typesCompletionCounitIso.hom.app F).app A =
      (typesCompletionCounit.app F).app A := rfl

/-- Each component of the counit is an isomorphism. -/
instance typesCompletionCounit_isIso (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (A : ArtinianLocalAlgCat Λ k) :
    IsIso ((typesCompletionCounit.app F).app A) :=
  Iso.isIso_hom (typesCompletionCounitIsoApp F A)

end CategoryTheory.Functor
