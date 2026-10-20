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

/-- Images of a point under the quotient maps form a compatible truncation tower. -/
theorem typesCompletionUnit_compatible (G : CompleteLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) (x : G.obj S) :
    ∀ (j j' : ℕᵒᵖ) (f : j ⟶ j'),
      (S.truncationSystem ⋙ typesRestrictInclusion.obj G).map f
          (G.map (truncationToInclusion S j.unop) x) =
        G.map (truncationToInclusion S j'.unop) x := sorry

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
        (typesCompletion (typesRestrictInclusion.obj G)).map f := sorry

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
        (typesCompletionMap (typesRestrictInclusion.map α)).app S := sorry

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

/-- Nilpotency-stage evaluation is natural in the Artinian local algebra. -/
theorem typesCompletionCounit_app_naturality (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    (typesRestrictInclusion.obj (typesCompletion F)).map f ≫ (limit.π ((inclusion.obj B).truncationSystem ⋙ F)
      (op (nilpotencyIndex B)) ≫ F.map (truncationNilpotencyIso B).hom) =
      (limit.π ((inclusion.obj A).truncationSystem ⋙ F)
      (op (nilpotencyIndex A)) ≫ F.map (truncationNilpotencyIso A).hom) ≫ F.map f := sorry

/-- Nilpotency-stage evaluation is natural in the set-valued functor. -/
theorem typesCompletionCounit_naturality {F H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (α : F ⟶ H) (A : ArtinianLocalAlgCat Λ k) :
    (typesRestrictInclusion.map (typesCompletionMap α)).app A ≫ (limit.π ((inclusion.obj A).truncationSystem ⋙ H)
      (op (nilpotencyIndex A)) ≫ H.map (truncationNilpotencyIso A).hom) =
      (limit.π ((inclusion.obj A).truncationSystem ⋙ F)
      (op (nilpotencyIndex A)) ≫ F.map (truncationNilpotencyIso A).hom) ≫ α.app A := sorry

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
      𝟙 (typesRestrictInclusion.obj G) := sorry

/-- The unit of a completed functor followed by completion of the counit is the identity. -/
theorem typesCompletion_right_triangle (F : ArtinianLocalAlgCat Λ k ⥤ Type w) :
    typesCompletionUnit.app (typesCompletionFunctor.obj F) ≫
        typesCompletionFunctor.map (typesCompletionCounit.app F) =
      𝟙 (typesCompletionFunctor.obj F) := sorry

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
        F.map (toTruncation A j'.unop) x := sorry

/-- Evaluation followed by the quotient-image tower is the identity on completion. -/
theorem typesCompletionCounitIsoApp_hom_inv_id
    (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (A : ArtinianLocalAlgCat Λ k) :
    (typesCompletionCounit.app F).app A ≫ TypeCat.ofHom (fun x ↦
      Types.Limit.mk ((inclusion.obj A).truncationSystem ⋙ F)
        (fun j ↦ F.map (toTruncation A j.unop) x)
        (typesCompletionCounitIsoApp_compatible F A x)) =
      𝟙 ((typesCompletion F).obj (inclusion.obj A)) := sorry

/-- The quotient-image tower followed by evaluation is the identity on the original set. -/
theorem typesCompletionCounitIsoApp_inv_hom_id
    (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (A : ArtinianLocalAlgCat Λ k) :
    TypeCat.ofHom (fun x ↦
      Types.Limit.mk ((inclusion.obj A).truncationSystem ⋙ F)
        (fun j ↦ F.map (toTruncation A j.unop) x)
        (typesCompletionCounitIsoApp_compatible F A x)) ≫ (typesCompletionCounit.app F).app A = 𝟙 (F.obj A) := sorry

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
