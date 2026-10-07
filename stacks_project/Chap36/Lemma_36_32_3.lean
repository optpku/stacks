module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.VectorBundleLocus

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 36.32.3: for a proper finitely presented morphism `f` and a finitely presented
module `ℱ` flat over the base, there is an open locus on which every base-changed derived
pushforward of `ℱ` is a vector bundle of rank `r` placed in degree `i`. -/
@[stacks 0B9S] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.exists_open_pushforward_isVectorBundleOfRankInDegree :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Scheme.Hom.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation] [SheafOfModules.IsFlatOver ℱ f.toShHom]
      (i r : ℤ),
      ∃ U : S.Opens, ∀ {T : Scheme.{u}} (g : T ⟶ S),
        (∃ lift : T ⟶ U.toScheme, lift ≫ U.ι = g) ↔
          AlgebraicGeometry.Scheme.ModuleDerived.IsVectorBundleOfRankInDegree
            ((RingedSpace.moduleDerivedPushforward (pullback.snd f g).toShHom).obj
              ((DerivedCategory.singleFunctor (pullback f g : Scheme.{u}).Modules 0).obj
                (Scheme.Modules.baseChangeModule f g ℱ))) i r)
