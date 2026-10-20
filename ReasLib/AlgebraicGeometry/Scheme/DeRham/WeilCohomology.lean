/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Cohomology.Functor
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CanonicalAction
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.Correspondence
public import ReasLib.AlgebraicGeometry.ChowCohomology
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Cycle
public import ReasLib.AlgebraicGeometry.ChowGroup.FieldFundamental
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {k : Type u} [Field k] [CharZero k]

/-- A classical theory realizes relative de Rham cohomology when its comparisons in every
cohomological degree and Tate twist preserve canonical pullback, the constant-one class,
wedge cup products, and Tate trivialization, and identify its integral Chow operations
with operational Chow cohomology and proper pushforward capped with fundamental classes. -/
def RealizesCohomology (T : WeilCohomology.SchemeClassicalTheory.Object k k) : Prop :=
  (fun (T : WeilCohomology.SchemeClassicalTheory.Object k k)
    (S : T.V ⥤ SchemeOverField k)
    (pullback : ∀ (X Y : T.V), (X ⟶ Y) → T.H Y → T.H X)
    (twist : ∀ X i j,
      TensorProduct k (T.Hgrade X (i, j)) T.TateLine ≃ₗ[k] T.Hgrade X (i, j + 1)) =>
  (∃ (comparison : ∀ (X : T.V) (i j : ℤ), T.Hgrade X (i, j) ≃ₗ[k]
        cohomologyOverAffineBase (A := CommRingCat.of k) (S.obj X).hom i)
      (tate : T.TateLine ≃ₗ[k] k),
    (∀ (X Y : T.V) (f : X ⟶ Y) (i j : ℤ) (a : T.Hgrade Y (i, j)),
      ((comparison X i j).toEquiv.symm
        ((Cohomology.pullbackOverField (k := k)
          (X := S.obj X) (Y := S.obj Y)
          (S.map f) i).hom
          (comparison Y i j a))).val = pullback X Y f a) ∧
    (∀ X, ((comparison X 0 0).toEquiv.symm
      (ClassAction.cohomologyOneCanonical (S.obj X).hom)).val = 1) ∧
    (∀ X i i' j j' (a : T.Hgrade X (i, j)) (b : T.Hgrade X (i', j')),
      ((comparison X (i + i') (j + j')).toEquiv.symm
        ((CanonicalAction.cupMorphism (S.obj X).hom i i').hom
          (TensorProduct.tmul (coefficientRing (S.obj X).hom)
            (comparison X i j a) (comparison X i' j' b)))).val =
        (a : T.H X) * b) ∧
    (∀ X i j (a : T.Hgrade X (i, j)) (t : T.TateLine),
      comparison X i (j + 1) (twist X i j (TensorProduct.tmul k a t)) =
        tate t • comparison X i j a))) T (@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory)
    (fun _ _ f a ↦ (@WeilCohomology.SchemeClassicalTheory.pullback k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory) f a) (@WeilCohomology.SchemeClassicalTheory.tateTwist k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory) ∧
  (fun (T : WeilCohomology.SchemeClassicalTheory.Object k k)
    [_finite : ∀ X : T.V, LocallyOfFiniteType ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).obj X).hom] =>
  ∃ ch : ∀ (X : T.V) (i : ℤ), T.CHgrade X i ≃
      ChowCohomology.degree (fun _ ↦ 0) ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).obj X).hom i,
    (∀ X i, ch X i 0 =
      ChowCohomology.zeroClass (fun _ ↦ 0) ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).obj X).hom i) ∧
    (∀ X i (a b : T.CHgrade X i), ch X i (a + b) =
      ChowCohomology.addClass (fun _ ↦ 0) ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).obj X).hom
        (ch X i a) (ch X i b)) ∧
    (∀ X, ((ch X 0).symm
      (ChowCohomology.one (fun _ ↦ 0) ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).obj X).hom) : T.CH X) = 1) ∧
    (∀ X i j (a : T.CHgrade X i) (b : T.CHgrade X j),
      ((ch X (i + j)).symm
        (ChowCohomology.mul (fun _ ↦ 0) ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).obj X).hom
          (ch X i a) (ch X j b)) : T.CH X) = (a : T.CH X) * b) ∧
    (∀ (X Y : T.V) (f : X ⟶ Y) i (a : T.CHgrade Y i),
      ((ch X i).symm
        (BivariantClass.restrict (fun _ ↦ 0) ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).map f) (𝟙 _) ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).map f) CategoryTheory.IsPullback.of_id_snd i
          (ch Y i a)) : T.CH X) = T.cyclePullback f a) ∧
    (∀ (X Y : T.V) (d e : ℕ)
      (hX : (@WeilCohomology.SchemeClassicalTheory.IsNonemptyEquidimensional k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory) X d)
      (hY : (@WeilCohomology.SchemeClassicalTheory.IsNonemptyEquidimensional k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory) Y e)
      (f : X ⟶ Y) [IsProper ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).map f).left]
      (i : ℤ) (a : T.CHgrade X i),
      HEq
        ((fun (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (d : ℕ) (i : ℤ) (a : ChowCohomology.degree (fun _ ↦ 0) X.hom i) =>
  a.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
    CategoryTheory.IsPullback.of_id_snd d
    (RelativeChow.fundamentalClass (fun _ ↦ 0) X d)) ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).obj Y) e (i + ((e : ℤ) - d))
          (ch Y (i + ((e : ℤ) - d))
            ⟨T.cyclePushforward f a, (@WeilCohomology.SchemeClassicalTheory.cyclePushforward_mem k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory) hX hY f i a⟩))
        (ChowGroup.map (fun _ ↦ 0) ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).obj X) ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).obj Y)
          ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).map f) ((d : ℤ) - i)
          ((fun (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (d : ℕ) (i : ℤ) (a : ChowCohomology.degree (fun _ ↦ 0) X.hom i) =>
  a.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
    CategoryTheory.IsPullback.of_id_snd d
    (RelativeChow.fundamentalClass (fun _ ↦ 0) X d)) ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).obj X) d i (ch X i a))))) T (_finite := fun (X : T.V) ↦ (fun {A B : Scheme.{u}} (f : A ⟶ B) [_smooth : Smooth f] ↦
    (inferInstance : LocallyOfFiniteType f)) ((@WeilCohomology.SchemeClassicalTheory.scheme k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory).obj X).hom
      (_smooth := (@WeilCohomology.SchemeClassicalTheory.smooth k _ k _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory) X))

/-- Over a characteristic-zero field, the canonical graded relative de Rham functor
admits a classical Weil cohomology structure with its canonical operations. -/
theorem existsWeilTheory (k : Type u) [Field k] [CharZero k] :
    ∃ T : WeilCohomology.SchemeClassicalTheory.Object k k,
      T.IsWeil ∧ RealizesCohomology T := by
  sorry

end AlgebraicGeometry.Scheme.DeRham
