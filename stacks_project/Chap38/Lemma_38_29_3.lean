/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalCompletion.Cohomology
public import stacks_project.Chap38.Lemma_38_29_2
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.DerivedCategory
open RingedSite.Hom.DerivedAdjunction
open RingedSpace.moduleDerivedPushforward.Composition

noncomputable section

universe u

/- Lemma 38.29.3 (1): in a formal-completion system, tensoring the
quasi-coherent coreflection of the homotopy limit with a perfect complex has
pseudo-coherent derived global sections over the limit ring. -/
@[stacks 0DID] #check
  (@AlgebraicGeometry.Scheme.ModuleDerived.FormalCompletion.System.globalSectionsTensorCoheratorHomotopyLimit_isPseudoCoherent :
    ∀ {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
      {X : Scheme.{u}} {f : X ⟶ Spec A_lim.cone.pt}
      [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
      {Xn : ℕ → Scheme.{u}} {p : ∀ n, Xn n ⟶ X}
      {q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n))}
      {i : ∀ n, Xn n ⟶ Xn (n + 1)}
      [∀ n, HasPair (RingedSpace.opensRingedSiteHom (i n).toShHom)]
      (S : Scheme.ModuleDerived.FormalCompletion.System A A_lim X f Xn p q i)
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
            (iso
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
      (E : RingedSpace.ModuleDerived X.toRingedSpace)
      (hE : RingedSpace.ModuleDerived.IsPerfect E),
      let K : DerivedCategory X.Modules :=
        ((@Functor.rightAdjoint _ _ _ _ (Scheme.DerivedQCoh.inclusion X)
          (@Scheme.DerivedQCoh.inclusionIsLeftAdjoint X
            (Scheme.Hom.compactSpace_of_finitePresentation f)
            (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj
      let M :=
        (AlgebraicGeometry.Scheme.FlatPullbackSections.baseSections f).obj
          (@DerivedTensor.Right.obj
            X.Modules _ _ _ _ _ _ K E (Scheme.Modules.hasDerivedTensorRight X))
      DerivedCategory.IsPseudoCoherent M)

/- Lemma 38.29.3 (2): at every infinitesimal stage, derived base change of
these global sections is isomorphic to the global sections of the stagewise
tensor product with the derived pullback of the perfect complex. -/
@[stacks 0DID] #check
  (@AlgebraicGeometry.Scheme.ModuleDerived.FormalCompletion.System.globalSectionsTensorCoheratorHomotopyLimit_nonemptyBaseChangeIso :
    ∀ {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
      {X : Scheme.{u}} {f : X ⟶ Spec A_lim.cone.pt}
      [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
      {Xn : ℕ → Scheme.{u}} {p : ∀ n, Xn n ⟶ X}
      {q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n))}
      {i : ∀ n, Xn n ⟶ Xn (n + 1)}
      [∀ n, HasPair (RingedSpace.opensRingedSiteHom (i n).toShHom)]
      (S : Scheme.ModuleDerived.FormalCompletion.System A A_lim X f Xn p q i)
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
            (iso
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
      (E : RingedSpace.ModuleDerived X.toRingedSpace)
      (hE : RingedSpace.ModuleDerived.IsPerfect E) (n : ℕ),
      let K : DerivedCategory X.Modules :=
        ((@Functor.rightAdjoint _ _ _ _ (Scheme.DerivedQCoh.inclusion X)
          (@Scheme.DerivedQCoh.inclusionIsLeftAdjoint X
            (Scheme.Hom.compactSpace_of_finitePresentation f)
            (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj
      let M :=
        (AlgebraicGeometry.Scheme.FlatPullbackSections.baseSections f).obj
          (@DerivedTensor.Right.obj
            X.Modules _ _ _ _ _ _ K E (Scheme.Modules.hasDerivedTensorRight X))
      let En (m : ℕ) : DerivedCategory (Xn m).Modules :=
        (RingedSpace.modulePullbackDerived (p m).toShHom).obj E
      let Mn (m : ℕ) :=
        (AlgebraicGeometry.Scheme.FlatPullbackSections.baseSections (q m)).obj
          (@DerivedTensor.Right.obj
            (Xn m).Modules _ _ _ _ _ _ (S.K m) (En m)
              (Scheme.Modules.hasDerivedTensorRight (Xn m)))
      Nonempty
        ((ModuleCat.derivedExtensionOfScalars (A_lim.cone.stageMap n).hom).obj M ≅
          Mn n))
