/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Types.Basic
public import stacks_project.Chap90.Remark_90_7_7_Nilpotency
public import stacks_project.Chap90.Remark_90_7_10_Functors

/-!
# Restriction ⊣ completion for Type-valued functors

The 1-functors `typesRestrictInclusion` and `typesCompletionFunctor` are adjoint.
The unit at `G` records the inverse-limit tower of images along
`truncationToInclusion`, and the counit at `F` evaluates the nilpotency-stage
projection and identifies it with `F` via `truncationNilpotencyIso`. The same
unit-then-map / restrict-then-counit construction as in the groupoid 2-adjunction
gives the hom-equivalence, and the counit is a natural isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite
open ArtinianLocalAlgCat CompleteLocalAlgCat

noncomputable section

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- The unit `G ⟶ hat(G|_{C_Λ})`, sending a point over `S` to the inverse-limit
tower of its images along `truncationToInclusion`. -/
def typesCompletionUnit :
    𝟭 (CompleteLocalAlgCat Λ k ⥤ Type w) ⟶
      typesRestrictInclusion ⋙ typesCompletionFunctor where
  app G :=
    { app S := TypeCat.ofHom fun x ↦
        Types.Limit.mk (S.truncationSystem ⋙ typesRestrictInclusion.obj G)
          (fun j ↦ G.map (truncationToInclusion S j.unop) x) sorry
      naturality := sorry }
  naturality := sorry

/-- The unit tower at stage `n` is the image along `truncationToInclusion`. -/
theorem typesCompletionUnit_app (G : CompleteLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) (x : G.obj S) (n : ℕ) :
    limit.π (S.truncationSystem ⋙ typesRestrictInclusion.obj G) (op n)
        ((typesCompletionUnit.app G).app S x) =
      G.map (truncationToInclusion S n) x := sorry

/-- The counit `hat F |_{C_Λ} ⟶ F`, evaluating the inverse limit at the nilpotency
stage and applying `F.map (truncationNilpotencyIso A).hom`. -/
def typesCompletionCounit :
    typesCompletionFunctor ⋙ typesRestrictInclusion ⟶
      𝟭 (ArtinianLocalAlgCat Λ k ⥤ Type w) where
  app F :=
    { app A :=
        limit.π ((inclusion.obj A).truncationSystem ⋙ F)
            (op (nilpotencyIndex A)) ≫
          F.map (truncationNilpotencyIso A).hom
      naturality := sorry }
  naturality := sorry

/-- The counit at `A` is the nilpotency-stage projection followed by the
nilpotency identification. -/
theorem typesCompletionCounit_app (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (A : ArtinianLocalAlgCat Λ k) :
    (typesCompletionCounit.app F).app A =
      limit.π ((inclusion.obj A).truncationSystem ⋙ F) (op (nilpotencyIndex A)) ≫
        F.map (truncationNilpotencyIso A).hom := sorry

/-- The source bijection `Mor_{C_Λ}(G|_{C_Λ}, F) ≃ Mor_{Ĉ_Λ}(G, hat F)`, sending
`α` to the unit followed by `hat α`, and sending `ψ` to the restriction of `ψ`
followed by the counit. -/
def typesCompletionHomEquiv (G : CompleteLocalAlgCat Λ k ⥤ Type w)
    (F : ArtinianLocalAlgCat Λ k ⥤ Type w) :
    (typesRestrictInclusion.obj G ⟶ F) ≃ (G ⟶ typesCompletionFunctor.obj F) where
  toFun α := typesCompletionUnit.app G ≫ typesCompletionFunctor.map α
  invFun ψ := typesRestrictInclusion.map ψ ≫ typesCompletionCounit.app F
  left_inv := sorry
  right_inv := sorry

/-- `typesCompletionHomEquiv` sends `α` to the unit followed by completion of `α`. -/
theorem typesCompletionHomEquiv_apply (G : CompleteLocalAlgCat Λ k ⥤ Type w)
    (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (α : typesRestrictInclusion.obj G ⟶ F) :
    typesCompletionHomEquiv G F α =
      typesCompletionUnit.app G ≫ typesCompletionFunctor.map α := sorry

/-- The inverse of `typesCompletionHomEquiv` sends `ψ` to the restriction of `ψ`
followed by the counit. -/
theorem typesCompletionHomEquiv_symm_apply (G : CompleteLocalAlgCat Λ k ⥤ Type w)
    (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (ψ : G ⟶ typesCompletionFunctor.obj F) :
    (typesCompletionHomEquiv G F).symm ψ =
      typesRestrictInclusion.map ψ ≫ typesCompletionCounit.app F := sorry

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
  left_triangle_components := sorry
  right_triangle_components := sorry

/-- The unit of `typesCompletionAdjunction` is `typesCompletionUnit`. -/
theorem typesCompletionAdjunction_unit :
    typesCompletionAdjunction.unit =
      (typesCompletionUnit :
        𝟭 (CompleteLocalAlgCat Λ k ⥤ Type w) ⟶
          typesRestrictInclusion ⋙ typesCompletionFunctor) := sorry

/-- The counit of `typesCompletionAdjunction` is `typesCompletionCounit`. -/
theorem typesCompletionAdjunction_counit :
    typesCompletionAdjunction.counit =
      (typesCompletionCounit :
        typesCompletionFunctor ⋙ typesRestrictInclusion ⟶
          𝟭 (ArtinianLocalAlgCat Λ k ⥤ Type w)) := sorry

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

/-- The objectwise inverse of the counit, sending a point of `F(A)` to the
truncation tower `F.map (toTruncation A n)`. -/
def typesCompletionCounitIsoApp (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (A : ArtinianLocalAlgCat Λ k) :
    (typesCompletion F).obj (inclusion.obj A) ≅ F.obj A where
  hom := (typesCompletionCounit.app F).app A
  inv := TypeCat.ofHom fun x ↦
    Types.Limit.mk ((inclusion.obj A).truncationSystem ⋙ F)
      (fun j ↦ F.map (toTruncation A j.unop) x) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The hom of `typesCompletionCounitIsoApp` is the counit component. -/
theorem typesCompletionCounitIsoApp_hom (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (A : ArtinianLocalAlgCat Λ k) :
    (typesCompletionCounitIsoApp F A).hom = (typesCompletionCounit.app F).app A := sorry

/-- The inverse of `typesCompletionCounitIsoApp` projects at stage `n` to
`F.map (toTruncation A n)`. -/
theorem typesCompletionCounitIsoApp_inv (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (A : ArtinianLocalAlgCat Λ k) (x : F.obj A) (n : ℕ) :
    limit.π ((inclusion.obj A).truncationSystem ⋙ F) (op n)
        ((typesCompletionCounitIsoApp F A).inv x) =
      F.map (toTruncation A n) x := sorry

/-- The counit `hat F |_{C_Λ} ⟶ F` is a natural isomorphism. -/
def typesCompletionCounitIso :
    typesCompletionFunctor ⋙ typesRestrictInclusion ≅
      𝟭 (ArtinianLocalAlgCat Λ k ⥤ Type w) :=
  NatIso.ofComponents
    (fun F ↦ NatIso.ofComponents (fun A ↦ typesCompletionCounitIsoApp F A) sorry) sorry

/-- The hom of `typesCompletionCounitIso` at `F` and `A` is the counit component. -/
theorem typesCompletionCounitIso_hom_app (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (A : ArtinianLocalAlgCat Λ k) :
    (typesCompletionCounitIso.hom.app F).app A =
      (typesCompletionCounit.app F).app A := sorry

/-- Each component of the counit is an isomorphism. -/
instance typesCompletionCounit_isIso (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (A : ArtinianLocalAlgCat Λ k) :
    IsIso ((typesCompletionCounit.app F).app A) :=
  Iso.isIso_hom (typesCompletionCounitIsoApp F A)

end CategoryTheory.Functor
