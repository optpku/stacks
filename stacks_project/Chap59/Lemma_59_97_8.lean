module

public import Mathlib.Algebra.Field.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
public import stacks_project.Chap59.Lemma_59_92_3_BaseChange
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Adjunction.Derived
open CategoryTheory.Sheaf
open CategoryTheory.DerivedCategory

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme.Hom

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
variable [MonoidalCategory (DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
variable [MonoidalCategory (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
variable [(zmodDerivedInverseImage h n).OplaxMonoidal]

/-- The canonical comparison
`p⁻¹ E ⊗ (f')⁻¹ R g_* F ⟶ R h_* (h⁻¹ p⁻¹ E ⊗ e⁻¹ F)`
in `D(X'_étale, ZMod n)`. It tensors the derived étale `ZMod n`
base-change component along the cartesian square of `g` with `p⁻¹ E`
on the left, then applies the projection-formula mate of the derived
adjunction for `h`. -/
noncomputable def etaleDerivedTensorBaseChangeHom
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    (zmodDerivedInverseImage p n).obj E ⊗
        (zmodDerivedInverseImage f' n).obj ((zmodDerivedPushforward g n).obj F) ⟶
      (zmodDerivedPushforward h n).obj
        ((zmodDerivedInverseImage h n).obj ((zmodDerivedInverseImage p n).obj E) ⊗
          (zmodDerivedInverseImage e n).obj F) :=
  let E' := (zmodDerivedInverseImage p n).obj E
  (𝟙 E' ⊗ₘ zmodDerivedBaseChangeHom g f' h e h_right.flip n F) ≫
    (KInjective.adjunction (zmodPullbackExact h n) (zmodSheafPushforward h n)
        (zmodSheafAdjunction h n)).projectionFormulaMate
      E' ((zmodDerivedInverseImage e n).obj F)

/-- `etaleDerivedTensorBaseChangeHom` is the whiskering of
`zmodDerivedBaseChangeHom` by the left tensor factor `p⁻¹ E`, followed by
the projection-formula mate for `h`. -/
theorem etaleDerivedTensorBaseChangeHom_eq
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    etaleDerivedTensorBaseChangeHom p f' g h e h_right n E F =
      (𝟙 ((zmodDerivedInverseImage p n).obj E) ⊗ₘ
          zmodDerivedBaseChangeHom g f' h e h_right.flip n F) ≫
        (KInjective.adjunction (zmodPullbackExact h n) (zmodSheafPushforward h n)
            (zmodSheafAdjunction h n)).projectionFormulaMate
          ((zmodDerivedInverseImage p n).obj E)
          ((zmodDerivedInverseImage e n).obj F) := sorry

/-- Lemma 59.97.8: if `K` is a field, `n ≥ 1` is invertible in `K`, and
the diagram of finite type `K`-schemes has cartesian squares
`IsPullback p f' x s` and `IsPullback h e f' g` with
`X' = X ×_{Spec K} S'` and `Y = X' ×_{S'} T`, then for `E` in
`D(X_étale, ZMod n)` and `F` in `D(T_étale, ZMod n)` the canonical map
`p⁻¹ E ⊗ (f')⁻¹ R g_* F ⟶ R h_* (h⁻¹ p⁻¹ E ⊗ e⁻¹ F)` is an
isomorphism. -/
@[stacks 0F1N]
theorem etaleDerivedTensorBaseChangeHom_isIso_of_finiteType_overField
    {k : Type u} [Field k] (x : X ⟶ Spec (CommRingCat.of k))
    (s : S' ⟶ Spec (CommRingCat.of k))
    [FiniteType x] [FiniteType s] [FiniteType (g ≫ s)] [FiniteType (p ≫ x)]
    [FiniteType (e ≫ g ≫ s)] (hn : 0 < n) (h_n : IsUnit (n : k))
    (h_left : IsPullback p f' x s)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    IsIso (etaleDerivedTensorBaseChangeHom p f' g h e h_right n E F) := sorry

end

variable {k : Type u} [Field k] {X S' T : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of k)) (s : S' ⟶ Spec (CommRingCat.of k))
variable (g : T ⟶ S') (n : ℕ)
variable [HasPullback x s] [HasPullback (pullback.snd x s) g]
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory.{w} (Sheaf S'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory.{w} (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory.{w}
    (Sheaf (pullback x s).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory.{w}
    (Sheaf (pullback (pullback.snd x s) g).smallEtaleTopology
      (ModuleCat.{u} (ZMod n)))]
variable [IsGrothendieckAbelian.{w} (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [IsGrothendieckAbelian.{w}
    (Sheaf (pullback (pullback.snd x s) g).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [MonoidalCategory
    (DerivedCategory (Sheaf (pullback x s).smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
variable [MonoidalCategory
    (DerivedCategory
      (Sheaf (pullback (pullback.snd x s) g).smallEtaleTopology
        (ModuleCat.{u} (ZMod n))))]
variable [(zmodDerivedInverseImage (pullback.fst (pullback.snd x s) g) n).OplaxMonoidal]

/-- Specialization of `etaleDerivedTensorBaseChangeHom_isIso_of_finiteType_overField`
to the chosen fibre products `pullback x s` and
`pullback (pullback.snd x s) g`, with `f' = pullback.snd x s`,
`h = pullback.fst (pullback.snd x s) g`, and
`e = pullback.snd (pullback.snd x s) g`. -/
theorem etaleDerivedTensorBaseChangeHom_isIso_of_finiteType_overField_pullback
    [FiniteType x] [FiniteType s] [FiniteType (g ≫ s)]
    [FiniteType (pullback.fst x s ≫ x)]
    [FiniteType (pullback.snd (pullback.snd x s) g ≫ g ≫ s)]
    (hn : 0 < n) (h_n : IsUnit (n : k))
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    IsIso
      (etaleDerivedTensorBaseChangeHom (pullback.fst x s) (pullback.snd x s) g
        (pullback.fst (pullback.snd x s) g) (pullback.snd (pullback.snd x s) g)
        (IsPullback.of_hasPullback (pullback.snd x s) g) n E F) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
