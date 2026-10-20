/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Tensor
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Sheaf CategoryTheory.DerivedCategory
open CategoryTheory.Adjunction.Derived ComplexShape
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u w

section

variable {X S' T X' Y : Scheme.{u}}
variable (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
variable (h_right : IsPullback h e f' g) (n : ℕ)
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory.{w} (Sheaf S'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory.{w} (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory.{w} (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory.{w} (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [IsGrothendieckAbelian.{w} (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [IsGrothendieckAbelian.{w} (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [(X'.smallEtaleTopology.W (A := ModuleCat.{u} (ZMod n))).IsMonoidal]
variable [MonoidalPreadditive (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [∀ G₁ G₂ : GradedObject ℤ (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
variable [DerivedTensor.Bifunctor.Has (C := (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
variable [(Y.smallEtaleTopology.W (A := ModuleCat.{u} (ZMod n))).IsMonoidal]
variable [MonoidalPreadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [∀ G₁ G₂ : GradedObject ℤ (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
variable [DerivedTensor.Bifunctor.Has (C := (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))))]


/- Lemma 59.97.8. The canonical derived étale tensor base-change map is an
isomorphism for arbitrary unbounded complexes on finite-type schemes over a field
with positive invertible coefficients. -/
@[stacks 0F1N] #check
  (AlgebraicGeometry.Scheme.Hom.etaleDerivedTensorBaseChangeHom_isIso_of_finiteType_overField
    p f' g h e h_right n :
    ∀ {k : Type u} [Field k] (x : X ⟶ Spec (CommRingCat.of k))
      (s : S' ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Scheme.Hom.FiniteType x]
      [AlgebraicGeometry.Scheme.Hom.FiniteType s]
      [AlgebraicGeometry.Scheme.Hom.FiniteType (g ≫ s)]
      [AlgebraicGeometry.Scheme.Hom.FiniteType (p ≫ x)]
      [AlgebraicGeometry.Scheme.Hom.FiniteType (e ≫ g ≫ s)],
      0 < n → IsUnit (n : k) → IsPullback p f' x s →
      ∀ (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
        (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))),
        IsIso (AlgebraicGeometry.Scheme.Etale.derivedTensorBaseChangeHom
          p f' g h e h_right n E F))

#check (AlgebraicGeometry.Scheme.Etale.derivedTensorBaseChangeHom p f' g h e h_right n :
  ∀ (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))),
    DerivedTensor.Bifunctor.obj
      ((zmodDerivedInverseImage p n).obj E)
      ((zmodDerivedInverseImage f' n).obj ((zmodDerivedPushforward g n).obj F)) ⟶
    (zmodDerivedPushforward h n).obj
      (DerivedTensor.Bifunctor.obj
        ((zmodDerivedInverseImage h n).obj ((zmodDerivedInverseImage p n).obj E))
        ((zmodDerivedInverseImage e n).obj F)))

#check (AlgebraicGeometry.Scheme.Etale.derivedTensorBaseChangeHom_eq p f' g h e h_right n :
  ∀ (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))),
    derivedTensorBaseChangeHom p f' g h e h_right n E F =
      (KInjective.adjunction (zmodPullbackExact h n)
        (zmodSheafPushforward h n) (zmodSheafAdjunction h n)).homEquiv _ _
        (zmodDerivedInverseImageTensorHom h n
            ((zmodDerivedInverseImage p n).obj E)
            ((zmodDerivedInverseImage f' n).obj ((zmodDerivedPushforward g n).obj F)) ≫
          DerivedTensor.Bifunctor.functor.map (Prod.mkHom (𝟙 _)
            ((zmodDerivedInverseImage h n).map
                (zmodDerivedBaseChangeHom g f' h e h_right.flip n F) ≫
              (KInjective.adjunction (zmodPullbackExact h n)
                (zmodSheafPushforward h n) (zmodSheafAdjunction h n)).counit.app
                  ((zmodDerivedInverseImage e n).obj F)))))

end

section

variable {k : Type u} [Field k] {X S' T : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of k)) (s : S' ⟶ Spec (CommRingCat.of k))
variable (g : T ⟶ S') (n : ℕ)
variable [HasPullback x s] [HasPullback (pullback.snd x s) g]
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory.{w} (Sheaf S'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory.{w} (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory.{w} (Sheaf (pullback x s).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory.{w} (Sheaf (pullback (pullback.snd x s) g).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [IsGrothendieckAbelian.{w} (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [IsGrothendieckAbelian.{w} (Sheaf (pullback (pullback.snd x s) g).smallEtaleTopology
  (ModuleCat.{u} (ZMod n)))]
variable [((pullback x s).smallEtaleTopology.W (A := ModuleCat.{u} (ZMod n))).IsMonoidal]
variable [MonoidalPreadditive (Sheaf (pullback x s).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [∀ G₁ G₂ : GradedObject ℤ (Sheaf (pullback x s).smallEtaleTopology (ModuleCat.{u} (ZMod n))), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf (pullback x s).smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf (pullback x s).smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (Sheaf (pullback x s).smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := (Sheaf (pullback x s).smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
variable [DerivedTensor.Bifunctor.Has (C := (Sheaf (pullback x s).smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
variable [((pullback (pullback.snd x s) g).smallEtaleTopology.W (A := ModuleCat.{u} (ZMod n))).IsMonoidal]
variable [MonoidalPreadditive (Sheaf (pullback (pullback.snd x s) g).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [∀ G₁ G₂ : GradedObject ℤ (Sheaf (pullback (pullback.snd x s) g).smallEtaleTopology (ModuleCat.{u} (ZMod n))), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf (pullback (pullback.snd x s) g).smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf (pullback (pullback.snd x s) g).smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (Sheaf (pullback (pullback.snd x s) g).smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := (Sheaf (pullback (pullback.snd x s) g).smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
variable [DerivedTensor.Bifunctor.Has (C := (Sheaf (pullback (pullback.snd x s) g).smallEtaleTopology (ModuleCat.{u} (ZMod n))))]


#check
  (AlgebraicGeometry.Scheme.Hom.etaleDerivedTensorBaseChangeHom_isIso_of_finiteType_overField_pullback
    x s g n :
    ∀ [AlgebraicGeometry.Scheme.Hom.FiniteType x]
      [AlgebraicGeometry.Scheme.Hom.FiniteType s]
      [AlgebraicGeometry.Scheme.Hom.FiniteType (g ≫ s)]
      [AlgebraicGeometry.Scheme.Hom.FiniteType (pullback.fst x s ≫ x)]
      [AlgebraicGeometry.Scheme.Hom.FiniteType
        (pullback.snd (pullback.snd x s) g ≫ g ≫ s)],
      0 < n → IsUnit (n : k) →
      ∀ (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
        (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))),
        IsIso
          (AlgebraicGeometry.Scheme.Etale.derivedTensorBaseChangeHom
            (pullback.fst x s) (pullback.snd x s) g
            (pullback.fst (pullback.snd x s) g) (pullback.snd (pullback.snd x s) g)
            (IsPullback.of_hasPullback (pullback.snd x s) g) n E F))

end
