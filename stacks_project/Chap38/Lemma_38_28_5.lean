/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalCompletion.OpenSections

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 38.28.5: in Situation 38.28.1, for every quasi-compact open `U ⊆ X`
and stage `n`, derived sections of the coherator homotopy limit on `U`, after
derived extension of scalars to `Aₙ`, are isomorphic to derived sections of
`ℱ n` on the inverse-image open `p n ⁻¹ᵁ U`. -/
@[stacks 0CTG] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.openSectionsCoheratorLimit_nonemptyBaseChangeIso :
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
      (U : X.Opens) [QuasiCompact U.ι] (n : ℕ),
    let K : DerivedCategory X.Modules :=
      ((@Functor.rightAdjoint _ _ _ _ (ModuleDerived.Quasicoherent.inclusion X)
        (@inclusionIsLeftAdjoint X
          (Scheme.Hom.compactSpace_of_finitePresentation f)
          (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj
    let Un : (Xn n).Opens := p n ⁻¹ᵁ U
    let Fn := (DerivedCategory.singleFunctor (Xn n).Modules (0 : ℤ)).obj (ℱ n)
    let M :=
      (FlatPullbackSections.baseSections (U.ι ≫ f)).obj
        ((Modules.Kunneth.pullbackDerived U.ι).obj K)
    let Mn :=
      (FlatPullbackSections.baseSections (Un.ι ≫ q n)).obj
        ((Modules.Kunneth.pullbackDerived Un.ι).obj Fn)
    Nonempty
      ((ModuleCat.derivedExtensionOfScalars (A_lim.cone.stageMap n).hom).obj M ≅ Mn))

end AlgebraicGeometry.Scheme.DerivedQCoh
