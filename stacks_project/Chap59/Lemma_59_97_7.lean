/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
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
in `D(X'_étale, ZMod n)`, after `Plus.ι`. It tensors the derived étale
`ZMod n` base-change component along the cartesian square of `g` with
`p⁻¹ E` on the left, then applies the projection-formula mate of the
derived adjunction for `h`. -/
noncomputable def etaleDerivedTensorBaseChangeHom
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (F : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    (zmodDerivedInverseImage p n).obj (DerivedCategory.Plus.ι.obj E) ⊗
        (zmodDerivedInverseImage f' n).obj
          ((zmodDerivedPushforward g n).obj (DerivedCategory.Plus.ι.obj F)) ⟶
      (zmodDerivedPushforward h n).obj
        ((zmodDerivedInverseImage h n).obj
            ((zmodDerivedInverseImage p n).obj (DerivedCategory.Plus.ι.obj E)) ⊗
          (zmodDerivedInverseImage e n).obj (DerivedCategory.Plus.ι.obj F)) :=
  let E' := (zmodDerivedInverseImage p n).obj (DerivedCategory.Plus.ι.obj E)
  let F' := DerivedCategory.Plus.ι.obj F
  (𝟙 E' ⊗ₘ zmodDerivedBaseChangeHom g f' h e h_right.flip n F') ≫
    (KInjective.adjunction (zmodPullbackExact h n) (zmodSheafPushforward h n)
        (zmodSheafAdjunction h n)).projectionFormulaMate
      E' ((zmodDerivedInverseImage e n).obj F')

/-- `etaleDerivedTensorBaseChangeHom` is the whiskering of
`zmodDerivedBaseChangeHom` by the left tensor factor `p⁻¹ E`, followed by
the projection-formula mate for `h`. -/
theorem etaleDerivedTensorBaseChangeHom_eq
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (F : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    etaleDerivedTensorBaseChangeHom p f' g h e h_right n E F =
      (𝟙 ((zmodDerivedInverseImage p n).obj (DerivedCategory.Plus.ι.obj E)) ⊗ₘ
          zmodDerivedBaseChangeHom g f' h e h_right.flip n
            (DerivedCategory.Plus.ι.obj F)) ≫
        (KInjective.adjunction (zmodPullbackExact h n) (zmodSheafPushforward h n)
            (zmodSheafAdjunction h n)).projectionFormulaMate
          ((zmodDerivedInverseImage p n).obj (DerivedCategory.Plus.ι.obj E))
          ((zmodDerivedInverseImage e n).obj (DerivedCategory.Plus.ι.obj F)) := sorry

/-- Lemma 59.97.7: if `K` is a field, `n ≥ 1` is invertible in `K`, the squares
`IsPullback p f' x s` and `IsPullback h e f' g` are cartesian with
`X' = X ×_{Spec K} S'` and `Y = X' ×_{S'} T`, and `g` is quasi-compact and
quasi-separated, then for `E` in `D⁺(X_étale, ZMod n)` of Tor-amplitude in
`[a, ∞]` and `F` in `D⁺(T_étale, ZMod n)`, the canonical map
`p⁻¹ E ⊗ (f')⁻¹ R g_* F ⟶ R h_* (h⁻¹ p⁻¹ E ⊗ e⁻¹ F)` is an isomorphism. -/
@[stacks 0F1J]
theorem etaleDerivedTensorBaseChangeHom_isIso_of_qcqs_overField
    {k : Type u} [Field k] (x : X ⟶ Spec (CommRingCat.of k))
    (s : S' ⟶ Spec (CommRingCat.of k)) [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [∀ (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
        (ComplexShape.up ℤ)]
    [hXTensor :
      @DerivedTensor.Right.Has (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))
        _ _ _ _ _ _]
    (hn : 0 < n) (h_n : IsUnit (n : k)) (h_left : IsPullback p f' x s)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (a : ℤ)
    (hE : DerivedTensor.HasTorAmplitudeGE (DerivedCategory.Plus.ι.obj E) a)
    (F : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
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

/-- Specialization of `etaleDerivedTensorBaseChangeHom_isIso_of_qcqs_overField` to the
chosen fibre products `pullback x s` and `pullback (pullback.snd x s) g`, with
`f' = pullback.snd x s`, `h = pullback.fst (pullback.snd x s) g`, and
`e = pullback.snd (pullback.snd x s) g`. -/
theorem etaleDerivedTensorBaseChangeHom_isIso_of_qcqs_overField_pullback
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [∀ (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
        (ComplexShape.up ℤ)]
    [hXTensor :
      @DerivedTensor.Right.Has (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))
        _ _ _ _ _ _]
    (hn : 0 < n) (h_n : IsUnit (n : k))
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (a : ℤ)
    (hE : DerivedTensor.HasTorAmplitudeGE (DerivedCategory.Plus.ι.obj E) a)
    (F : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    IsIso
      (etaleDerivedTensorBaseChangeHom (pullback.fst x s) (pullback.snd x s) g
        (pullback.fst (pullback.snd x s) g) (pullback.snd (pullback.snd x s) g)
        (IsPullback.of_hasPullback (pullback.snd x s) g) n E F) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
