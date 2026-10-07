module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalCompletion.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator.HomotopyLimit.Thickenings
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.Tensor

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.DerivedCategory
open DerivedTensor.Right
open RingedSite.Hom.DerivedAdjunction
open RingedSpace.ModuleDerived.KFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Tensoring the coherator of the homotopy limit of a compatible formal thickening system
with a perfect object gives a perfect derived global-sections complex. -/
theorem globalSectionsTensorLimit_isPerfect
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
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
    (hE : RingedSpace.ModuleDerived.IsPerfect E) :
    let K : DerivedCategory X.Modules :=
      ((@Functor.rightAdjoint _ _ _ _ (ModuleDerived.Quasicoherent.inclusion X)
        (@inclusionIsLeftAdjoint X
          (Scheme.Hom.compactSpace_of_finitePresentation f)
          (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj
    DerivedCategory.IsPerfect
      ((Scheme.FlatPullbackSections.baseSections f).obj
        (@DerivedTensor.Right.obj X.Modules _ _ _ _ _ _ K E
          (Scheme.Modules.hasDerivedTensorRight X))) := sorry

/-- The canonical scalar-extension comparison for tensor global sections from a formal
homotopy limit to each closed-thickening stage is an isomorphism. -/
theorem globalSectionsTensorLimitBaseChangeMap_isIso
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
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
    (n : ℕ) :
    let K : DerivedCategory X.Modules :=
      ((@Functor.rightAdjoint _ _ _ _ (ModuleDerived.Quasicoherent.inclusion X)
        (@inclusionIsLeftAdjoint X
          (Scheme.Hom.compactSpace_of_finitePresentation f)
          (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj
    IsIso (globalSectionsTensorLimitBaseChangeMap A A_lim X f Xn p q h_pullback
      ℱ F stageIso Klim P E T_X T_Xn n) := sorry

/-- The derived global internal Hom from a perfect object into the coherator of a formal
homotopy limit is perfect over the inverse-limit ring. -/
theorem globalHomLimit_isPerfect
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
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
    (hE : RingedSpace.ModuleDerived.IsPerfect E) :
    let K : DerivedCategory X.Modules :=
      ((@Functor.rightAdjoint _ _ _ _ (ModuleDerived.Quasicoherent.inclusion X)
        (@inclusionIsLeftAdjoint X
          (Scheme.Hom.compactSpace_of_finitePresentation f)
          (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj
    DerivedCategory.IsPerfect
      ((Scheme.FlatPullbackSections.baseSections f).obj ((H_X.ihomOf E).obj K)) := sorry

/-- The canonical scalar-extension comparison for derived global internal Hom from a formal
homotopy limit to each closed-thickening stage is an isomorphism. -/
theorem globalHomLimitBaseChangeMap_isIso
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
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
    (n : ℕ) :
    let K : DerivedCategory X.Modules :=
      ((@Functor.rightAdjoint _ _ _ _ (ModuleDerived.Quasicoherent.inclusion X)
        (@inclusionIsLeftAdjoint X
          (Scheme.Hom.compactSpace_of_finitePresentation f)
          (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj
    IsIso (globalHomLimitBaseChangeMap A A_lim X f Xn p q h_pullback
      ℱ F stageIso Klim P E H_X H_Xn n) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
