module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.ZMod
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Sheaf CategoryTheory.DerivedCategory
open CategoryTheory.Adjunction.Derived ComplexShape
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

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

namespace Etale

/-- The derived tensor base-change morphism is the adjunction transpose of the
inverse-image tensor comparison followed by the base-change component and counit. -/
def derivedTensorBaseChangeHom
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    DerivedTensor.Bifunctor.obj
        ((zmodDerivedInverseImage p n).obj E)
        ((zmodDerivedInverseImage f' n).obj ((zmodDerivedPushforward g n).obj F)) ⟶
      (zmodDerivedPushforward h n).obj
        (DerivedTensor.Bifunctor.obj
          ((zmodDerivedInverseImage h n).obj ((zmodDerivedInverseImage p n).obj E))
          ((zmodDerivedInverseImage e n).obj F)) :=
  let A := (zmodDerivedInverseImage p n).obj E
  let B := (zmodDerivedInverseImage f' n).obj ((zmodDerivedPushforward g n).obj F)
  let C := (zmodDerivedInverseImage e n).obj F
  let b := zmodDerivedBaseChangeHom g f' h e h_right.flip n F
  let adj := KInjective.adjunction (zmodPullbackExact h n)
    (zmodSheafPushforward h n) (zmodSheafAdjunction h n)
  adj.homEquiv _ _
    (zmodDerivedInverseImageTensorHom h n A B ≫
      DerivedTensor.Bifunctor.functor.map (Prod.mkHom (𝟙 _)
        ((zmodDerivedInverseImage h n).map b ≫ adj.counit.app C)))

/-- The complete defining adjunction-mate formula for derived tensor base change. -/
theorem derivedTensorBaseChangeHom_eq
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
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
                  ((zmodDerivedInverseImage e n).obj F)))) := rfl

end Etale

variable [(X.smallEtaleTopology.W (A := ModuleCat.{u} (ZMod n))).IsMonoidal]
variable [MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [∀ K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))) ℤ,
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) (up ℤ)]
variable [DerivedTensor.Right.Has (C := Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]

namespace Hom

/-- Over a field with positive invertible coefficients, derived tensor base change
along two cartesian squares is invertible for bounded-below inputs whose first
factor has a lower Tor-amplitude bound, provided the base morphism is quasi-compact
and quasi-separated. -/
@[stacks 0F1J]
theorem etaleDerivedTensorBaseChangeHom_isIso_of_qcqs_overField
    {k : Type u} [Field k] (x : X ⟶ Spec (CommRingCat.of k))
    (s : S' ⟶ Spec (CommRingCat.of k)) [QuasiCompact g] [QuasiSeparated g]
    (hn : 0 < n) (h_n : IsUnit (n : k)) (h_left : IsPullback p f' x s)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (a : ℤ) (hE : DerivedTensor.HasTorAmplitudeGE (DerivedCategory.Plus.ι.obj E) a)
    (F : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    IsIso (derivedTensorBaseChangeHom p f' g h e h_right n
      (DerivedCategory.Plus.ι.obj E) (DerivedCategory.Plus.ι.obj F)) := sorry

end Hom

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

variable [(X.smallEtaleTopology.W (A := ModuleCat.{u} (ZMod n))).IsMonoidal]
variable [MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [∀ K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))) ℤ,
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) (up ℤ)]
variable [DerivedTensor.Right.Has (C := Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]

namespace Hom

/-- Derived tensor base change is invertible on the chosen successive fibre products
over a field for bounded-below inputs with a lower Tor-amplitude bound on the
first factor and a quasi-compact quasi-separated base morphism. -/
theorem etaleDerivedTensorBaseChangeHom_isIso_of_qcqs_overField_pullback
    [QuasiCompact g] [QuasiSeparated g] (hn : 0 < n) (h_n : IsUnit (n : k))
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (a : ℤ) (hE : DerivedTensor.HasTorAmplitudeGE (DerivedCategory.Plus.ι.obj E) a)
    (F : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    IsIso
      (derivedTensorBaseChangeHom (pullback.fst x s) (pullback.snd x s) g
        (pullback.fst (pullback.snd x s) g) (pullback.snd (pullback.snd x s) g)
        (IsPullback.of_hasPullback (pullback.snd x s) g) n
        (DerivedCategory.Plus.ι.obj E) (DerivedCategory.Plus.ι.obj F)) :=
  etaleDerivedTensorBaseChangeHom_isIso_of_qcqs_overField
    (pullback.fst x s) (pullback.snd x s) g
    (pullback.fst (pullback.snd x s) g) (pullback.snd (pullback.snd x s) g)
    (IsPullback.of_hasPullback (pullback.snd x s) g) n x s hn h_n
    (IsPullback.of_hasPullback x s) E a hE F

end Hom

end

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


namespace Hom

/-- Over a field with positive invertible coefficients, the canonical derived
étale tensor base-change morphism along two cartesian squares of finite-type
schemes is invertible for arbitrary unbounded complexes. -/
@[stacks 0F1N]
theorem etaleDerivedTensorBaseChangeHom_isIso_of_finiteType_overField
    {k : Type u} [Field k] (x : X ⟶ Spec (CommRingCat.of k))
    (s : S' ⟶ Spec (CommRingCat.of k))
    [FiniteType x] [FiniteType s] [FiniteType (g ≫ s)] [FiniteType (p ≫ x)]
    [FiniteType (e ≫ g ≫ s)] (hn : 0 < n) (h_n : IsUnit (n : k))
    (h_left : IsPullback p f' x s)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    IsIso (Etale.derivedTensorBaseChangeHom p f' g h e h_right n E F) := sorry

end Hom

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


namespace Hom

/-- Over a field with positive invertible coefficients, canonical derived étale
tensor base change on the chosen successive fibre products of finite-type schemes
is invertible for arbitrary unbounded complexes. -/
theorem etaleDerivedTensorBaseChangeHom_isIso_of_finiteType_overField_pullback
    [FiniteType x] [FiniteType s] [FiniteType (g ≫ s)]
    [FiniteType (pullback.fst x s ≫ x)]
    [FiniteType (pullback.snd (pullback.snd x s) g ≫ g ≫ s)]
    (hn : 0 < n) (h_n : IsUnit (n : k))
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    IsIso
      (Etale.derivedTensorBaseChangeHom (pullback.fst x s) (pullback.snd x s) g
        (pullback.fst (pullback.snd x s) g) (pullback.snd (pullback.snd x s) g)
        (IsPullback.of_hasPullback (pullback.snd x s) g) n E F) :=
  etaleDerivedTensorBaseChangeHom_isIso_of_finiteType_overField
    (pullback.fst x s) (pullback.snd x s) g
    (pullback.fst (pullback.snd x s) g) (pullback.snd (pullback.snd x s) g)
    (IsPullback.of_hasPullback (pullback.snd x s) g) n x s hn h_n
    (IsPullback.of_hasPullback x s) E F

end Hom

end

end AlgebraicGeometry.Scheme
