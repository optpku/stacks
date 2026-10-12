/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.VectorBundleLocus
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.FlatCoefficients

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- For a proper finitely presented morphism and a finitely presented module flat over the
base, the locus where the base-changed derived pushforward is a vector bundle of fixed rank
placed in a fixed degree is open. -/
theorem exists_open_pushforward_isVectorBundleOfRankInDegree
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] [SheafOfModules.IsFlatOver ℱ f.toShHom]
    (i r : ℤ) :
    ∃ U : S.Opens, ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (∃ lift : T ⟶ U.toScheme, lift ≫ U.ι = g) ↔
        IsVectorBundleOfRankInDegree
          ((RingedSpace.moduleDerivedPushforward (pullback.snd f g).toShHom).obj
            ((DerivedCategory.singleFunctor (pullback f g : Scheme.{u}).Modules 0).obj
              (Scheme.Modules.baseChangeModule f g ℱ))) i r := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
