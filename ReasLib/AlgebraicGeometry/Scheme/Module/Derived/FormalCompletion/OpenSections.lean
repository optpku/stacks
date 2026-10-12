/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalCompletion.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalCompletion.Cohomology

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.DerivedCategory
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a compatible system of finitely presented flat modules on formal thickenings,
derived sections of the coherator homotopy limit over a quasi-compact open commute with
derived extension of scalars to every stage. -/
theorem openSectionsCoheratorLimit_nonemptyBaseChangeIso
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
    (U : X.Opens) [QuasiCompact U.ι] (n : ℕ) :
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
      ((ModuleCat.derivedExtensionOfScalars (A_lim.cone.stageMap n).hom).obj M ≅ Mn) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

namespace AlgebraicGeometry.Scheme.ModuleDerived.FormalCompletion.System

/-- For a formal-completion system of pseudo-coherent derived modules, derived
sections of the quasi-coherent coreflection of a homotopy limit over a
quasi-compact open commute with derived extension of scalars to every stage. -/
theorem openSectionsCoheratorHomotopyLimit_nonemptyBaseChangeIso
    {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
    {X : Scheme.{u}} {f : X ⟶ Spec A_lim.cone.pt}
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    {Xn : ℕ → Scheme.{u}} {p : ∀ n, Xn n ⟶ X}
    {q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n))}
    {i : ∀ n, Xn n ⟶ Xn (n + 1)}
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom (i n).toShHom)]
    (S : FormalCompletion.System A A_lim X f Xn p q i)
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom (p n).toShHom)]
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom
      ((i n).toShHom ≫ (p (n + 1)).toShHom))]
    (Ksys : SequentialInverseSystem (RingedSpace.ModuleDerived X.toRingedSpace))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (RingedSpace.moduleDerivedPushforward (p n).toShHom).obj (S.K n))
    (stageIso_naturality : ∀ n,
      Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫
          (RingedSpace.moduleDerivedPushforward (p (n + 1)).toShHom).map (S.φ n) ≫
          (RingedSpace.moduleDerivedPushforward.Composition.iso
            (i n).toShHom (p (n + 1)).toShHom
            (RingedSpace.modulePullbackDerived.compComparison_isIso
              (i n).toShHom (p (n + 1)).toShHom)).hom.app (S.K n) ≫
          eqToHom (congrArg
            (fun g ↦ (RingedSpace.moduleDerivedPushforward g).obj (S.K n))
            ((LocallyRingedSpace.comp_toShHom
              (i n).toLRSHom (p (n + 1)).toLRSHom).symm.trans
                ((congrArg (fun g ↦ g.toShHom)
                  (Scheme.Hom.comp_toLRSHom (i n) (p (n + 1)))).symm.trans
                    (congrArg (fun g : Xn n ⟶ X ↦ g.toShHom) (S.comp_p n))))))
    (Klim : RingedSpace.ModuleDerived X.toRingedSpace)
    (hKlim : HomotopyLimit.IsOf Ksys Klim)
    (U : X.Opens) [QuasiCompact U.ι] (n : ℕ) :
    let K : DerivedCategory X.Modules :=
      ((@Functor.rightAdjoint _ _ _ _ (Scheme.DerivedQCoh.inclusion X)
        (@Scheme.DerivedQCoh.inclusionIsLeftAdjoint X
          (Scheme.Hom.compactSpace_of_finitePresentation f)
          (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj
    let Un : (Xn n).Opens := p n ⁻¹ᵁ U
    let M :=
      (FlatPullbackSections.baseSections (U.ι ≫ f)).obj
        ((Modules.Kunneth.pullbackDerived U.ι).obj K)
    let Mn :=
      (FlatPullbackSections.baseSections (Un.ι ≫ q n)).obj
        ((Modules.Kunneth.pullbackDerived Un.ι).obj (S.K n))
    Nonempty
      ((ModuleCat.derivedExtensionOfScalars (A_lim.cone.stageMap n).hom).obj M ≅ Mn) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.FormalCompletion.System
