/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalCompletion.PseudoCoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 38.28.4: in Situation 38.28.1, the quasicoherent coreflection `K` of
the ambient derived inverse limit is pseudo-coherent relative to the limit ring. -/
@[stacks 0CTF] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.coheratorHomotopyLimit_isPseudoCoherentOver :
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
          DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) Klim),
      let K : Scheme.ModuleDerived.Quasicoherent X :=
        (@Functor.rightAdjoint _ _ _ _ (ModuleDerived.Quasicoherent.inclusion X)
          (@inclusionIsLeftAdjoint X
            (Scheme.Hom.compactSpace_of_finitePresentation f)
            (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim
      Scheme.ModuleDerived.IsPseudoCoherentOver f K.obj)

end AlgebraicGeometry.Scheme.DerivedQCoh
