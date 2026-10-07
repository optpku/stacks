module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalCompletion.OpenSections

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.DerivedCategory
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

/- Lemma 38.29.5: for a formal-completion system and every quasi-compact open
`U ⊆ X`, derived sections of the coherator homotopy limit on `U`, after
derived extension of scalars to the stage ring, are isomorphic to derived
sections of the stage object on `p n ⁻¹ᵁ U`. -/
@[stacks 0DIF] #check
  (@AlgebraicGeometry.Scheme.ModuleDerived.FormalCompletion.System.openSectionsCoheratorHomotopyLimit_nonemptyBaseChangeIso :
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
      (U : X.Opens) [QuasiCompact U.ι] (n : ℕ),
      let K : DerivedCategory X.Modules :=
        ((@Functor.rightAdjoint _ _ _ _ (Scheme.DerivedQCoh.inclusion X)
          (@Scheme.DerivedQCoh.inclusionIsLeftAdjoint X
            (Scheme.Hom.compactSpace_of_finitePresentation f)
            (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj Klim).obj
      let Un : (Xn n).Opens := p n ⁻¹ᵁ U
      let M :=
        (Scheme.FlatPullbackSections.baseSections (U.ι ≫ f)).obj
          ((Scheme.Modules.Kunneth.pullbackDerived U.ι).obj K)
      let Mn :=
        (Scheme.FlatPullbackSections.baseSections (Un.ι ≫ q n)).obj
          ((Scheme.Modules.Kunneth.pullbackDerived Un.ι).obj (S.K n))
      Nonempty
        ((ModuleCat.derivedExtensionOfScalars (A_lim.cone.stageMap n).hom).obj M ≅ Mn))
