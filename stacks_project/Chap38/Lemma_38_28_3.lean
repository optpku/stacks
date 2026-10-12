/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalCompletion.Perfect

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.DerivedCategory
open DerivedTensor.Right
open RingedSite.Hom.DerivedAdjunction
open RingedSpace.ModuleDerived.KFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 38.28.3 (1): in Situation 38.28.1, for the object `K` obtained by
quasicoherent coreflection of the derived inverse limit and every perfect `E`,
`RΓ(X, K ⊗ᴸ E)` is perfect over the inverse-limit ring. -/
@[stacks 0CTE] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.globalSectionsTensorLimit_isPerfect :
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
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E),
    let K : DerivedCategory X.Modules :=
      ((@Functor.rightAdjoint _ _ _ _ (ModuleDerived.Quasicoherent.inclusion X)
        (@inclusionIsLeftAdjoint X
          (Scheme.Hom.compactSpace_of_finitePresentation f)
          (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj
    DerivedCategory.IsPerfect
      ((Scheme.FlatPullbackSections.baseSections f).obj
        (@DerivedTensor.Right.obj X.Modules _ _ _ _ _ _ K E
          (Scheme.Modules.hasDerivedTensorRight X))))

/- Lemma 38.28.3 (2): the canonical comparison from derived scalar extension of
`RΓ(X, K ⊗ᴸ E)` to `RΓ(Xₙ, ℱₙ ⊗ᴸ Lpₙ^*E)` is invertible. -/
@[stacks 0CTE] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.globalSectionsTensorLimitBaseChangeMap_isIso :
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
    (P : HomotopyLimit.Presentation
      (F ⋙ Scheme.QCoh.inclusion X ⋙
        DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) Klim)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [∀ n, HomotopyTensorDescends (Xn n).toRingedSpace]
    [∀ n, TensorDescends (Xn n).toRingedSpace]
    [∀ n, IsLocalization (Xn n).toRingedSpace]
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom (p n).toShHom)]
    [∀ n, (RingedSpace.modulePullbackDerived (p n).toShHom).Monoidal]
    (T_X : @Monoidal.Model
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
    (T_Xn : ∀ n, @Monoidal.Model
      (RingedSpace.Modules (Xn n).toRingedSpace) _ _ _ _ _ _ _)
    (n : ℕ),
    let K : DerivedCategory X.Modules :=
      ((@Functor.rightAdjoint _ _ _ _ (ModuleDerived.Quasicoherent.inclusion X)
        (@inclusionIsLeftAdjoint X
          (Scheme.Hom.compactSpace_of_finitePresentation f)
          (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj
    IsIso (globalSectionsTensorLimitBaseChangeMap A A_lim X f Xn p q h_pullback
      ℱ F stageIso Klim P E T_X T_Xn n))

/- Lemma 38.28.3 (3): in Situation 38.28.1, for every perfect `E`, the
derived global Hom `RHom_X(E, K)` is perfect over the inverse-limit ring. -/
@[stacks 0CTE] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.globalHomLimit_isPerfect :
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
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    (H_X : @MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace) _
      (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace))
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E),
    let K : DerivedCategory X.Modules :=
      ((@Functor.rightAdjoint _ _ _ _ (ModuleDerived.Quasicoherent.inclusion X)
        (@inclusionIsLeftAdjoint X
          (Scheme.Hom.compactSpace_of_finitePresentation f)
          (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj
    DerivedCategory.IsPerfect
      ((Scheme.FlatPullbackSections.baseSections f).obj ((H_X.ihomOf E).obj K)))

/- Lemma 38.28.3 (4): the canonical comparison from derived scalar extension of
`RHom_X(E, K)` to `RHom_Xₙ(Lpₙ^*E, ℱₙ)` is invertible. -/
@[stacks 0CTE] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.globalHomLimitBaseChangeMap_isIso :
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
    (P : HomotopyLimit.Presentation
      (F ⋙ Scheme.QCoh.inclusion X ⋙
        DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) Klim)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [∀ n, HomotopyTensorDescends (Xn n).toRingedSpace]
    [∀ n, TensorDescends (Xn n).toRingedSpace]
    [∀ n, IsLocalization (Xn n).toRingedSpace]
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom (p n).toShHom)]
    [∀ n, (RingedSpace.modulePullbackDerived (p n).toShHom).Monoidal]
    (H_X : @MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace) _
      (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace))
    (H_Xn : ∀ n, @MonoidalClosed
      (RingedSpace.ModuleDerived (Xn n).toRingedSpace) _
      (RingedSpace.ModuleDerived.monoidalCategory (Xn n).toRingedSpace))
    (n : ℕ),
    let K : DerivedCategory X.Modules :=
      ((@Functor.rightAdjoint _ _ _ _ (ModuleDerived.Quasicoherent.inclusion X)
        (@inclusionIsLeftAdjoint X
          (Scheme.Hom.compactSpace_of_finitePresentation f)
          (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj
    IsIso (globalHomLimitBaseChangeMap A A_lim X f Xn p q h_pullback
      ℱ F stageIso Klim P E H_X H_Xn n))

end AlgebraicGeometry.Scheme.DerivedQCoh
