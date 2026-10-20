/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalCompletion.ProperSupport

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 38.28.7: after shrinking an open neighborhood supplied by Lemma 38.28.6, the
degree-zero cohomology of the coherator homotopy limit has proper support over the inverse-limit
affine base. -/
@[stacks 0CTI] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.existsOpen_coheratorLimit_hasProperSupport :
    ∀ (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
      (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
      (X : Scheme.{u}) (f : X ⟶ Spec A_lim.cone.pt)
      [IsSeparated f] [Scheme.Hom.FinitePresentation f]
      (Xn : ℕ → Scheme.{u}) (p : ∀ n, Xn n ⟶ X)
      (q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n)))
      (h_pullback : ∀ n,
        IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f)
      [∀ n, IsClosedImmersion (p n)]
      (i : ∀ n, Xn n ⟶ Xn (n + 1))
      (hiX : ∀ n, i n ≫ p (n + 1) = p n)
      (hiA : ∀ n, i n ≫ q (n + 1) = q n ≫ Spec.map (A.stepMap n))
      (ℱ : ∀ n, (Xn n).Modules) [∀ n, (ℱ n).IsFinitePresentation]
      (h_flat : ∀ n, Scheme.Modules.flatOver (ℱ n) (q n))
      [∀ n, Scheme.Modules.HasProperSupportOver (q n) (ℱ n)]
      (φ : ∀ n, (Scheme.Modules.pullback (i n)).obj (ℱ (n + 1)) ⟶ ℱ n)
      [∀ n, IsIso (φ n)]
      (F : SequentialInverseSystem (Scheme.QCoh X))
      (stageIso : ∀ n, F.obj (Opposite.op n) ≅
        (Scheme.QCoh.pushforward (p n)).obj
          (⟨ℱ n, inferInstance⟩ : Scheme.QCoh (Xn n)))
      (step_compat : ∀ n,
        (stageIso (n + 1)).inv.hom ≫ (F.stepMap n).hom ≫ (stageIso n).hom.hom =
          (Scheme.Modules.pushforward (p (n + 1))).map
              ((Scheme.Modules.pullbackPushforwardAdjunction (i n)).homEquiv _ _ (φ n)) ≫
            (Scheme.Modules.pushforwardComp (i n) (p (n + 1))).hom.app (ℱ n) ≫
            (Scheme.Modules.pushforwardCongr (hiX n)).hom.app (ℱ n))
      (Klim : RingedSpace.ModuleDerived X.toRingedSpace)
      (hKlim : HomotopyLimit.IsOf
        (F ⋙ Scheme.QCoh.inclusion X ⋙
          DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) Klim)
      (W : X.Opens)
      (hW : ∀ n, Set.range (p n).base ⊆ Set.range W.ι.base),
      let K : DerivedCategory X.Modules :=
        ((@Functor.rightAdjoint _ _ _ _ (ModuleDerived.Quasicoherent.inclusion X)
          (@inclusionIsLeftAdjoint X
            (Scheme.Hom.compactSpace_of_finitePresentation f)
            (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj
      let G := (Scheme.Modules.pullback W.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules 0).obj K)
      (h_concentrated : ∀ j : ℤ, j ≠ 0 →
        IsZero ((Scheme.Modules.pullback W.ι).obj
          ((DerivedCategory.homologyFunctor X.Modules j).obj K))) →
      (h_finitePresentation : G.IsFinitePresentation) →
      (h_stageIso : ∀ n, Nonempty
        ((Scheme.Modules.pullback (IsOpenImmersion.lift W.ι (p n) (hW n))).obj G ≅
          ℱ n)) →
      ∃ (W' : X.Opens)
          (hW'_le : W' ≤ W)
          (hW' : ∀ n, Set.range (p n).base ⊆ Set.range W'.ι.base),
        Scheme.Modules.HasProperSupportOver (W'.ι ≫ f)
          ((Scheme.Modules.pullback W'.ι).obj
            ((DerivedCategory.homologyFunctor X.Modules 0).obj K)))

end AlgebraicGeometry.Scheme.DerivedQCoh
