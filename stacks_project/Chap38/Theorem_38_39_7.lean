/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Colimit.Descent
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FrobeniusColimit

/- Theorem 38.39.7 (1): Pullback along a proper surjective morphism of finite presentation with
geometrically connected fibres is fully faithful on the Frobenius colimits of vector bundles. -/
@[stacks 0EXH]
#check
  (AlgebraicGeometry.Scheme.FrobeniusColimit.pullbackFullyFaithful :
    ∀ (p : ℕ) [Fact p.Prime]
        {X Y : Scheme.{u}} [Y.IsCharP p] [X.IsCharP p]
        [CompactSpace Y] [QuasiSeparatedSpace Y]
        (f : X ⟶ Y) [IsProper f] [Surjective f] [Scheme.Hom.FinitePresentation f]
        (_ : ∀ y : Y, GeometricallyConnected (f.fiberToSpecResidueField y))
        (G : vectorBundleColimit p Y ⥤ vectorBundleColimit p X)
        [IsStagewisePullback p f G],
      Nonempty G.FullyFaithful)

/- Theorem 38.39.7 (2): A finite locally free module whose restriction to every reduced fibre
becomes finite free after a fibre-dependent Frobenius pullback descends after one global
Frobenius pullback. -/
@[stacks 0EXH]
#check
  (AlgebraicGeometry.Scheme.FrobeniusColimit.eventuallyDescends :
    ∀ (p : ℕ) [Fact p.Prime]
        {X Y : Scheme.{u}} [Y.IsCharP p]
        [CompactSpace Y] [QuasiSeparatedSpace Y]
        (f : X ⟶ Y) [IsProper f] [Surjective f] [Scheme.Hom.FinitePresentation f]
        (_ : ∀ y : Y, GeometricallyConnected (f.fiberToSpecResidueField y))
        (E : X.Modules) [E.IsFiniteLocallyFree]
        (_ : ∀ y : Y, ∃ n_y r_y : ℕ,
          Nonempty
            ((Scheme.Modules.pullback
              (Scheme.reductionι (f.fiber y) ≫ f.fiberι y ≫
                @Scheme.Hom.absoluteFrobeniusPowSource p _ X Y f _ n_y)).obj E ≅
              SheafOfModules.freeFin r_y)),
      ∃ n : ℕ, ∃ F : Y.Modules, ∃ _ : F.IsFiniteLocallyFree,
        Nonempty
          ((Scheme.Modules.pullback
            (@Scheme.Hom.absoluteFrobeniusPowSource p _ X Y f _ n)).obj E ≅
            (Scheme.Modules.pullback f).obj F))

/- An explicit eventual descent isomorphism gives the essential-image formulation of the
preceding descent statement. -/
#check
  (AlgebraicGeometry.Scheme.FrobeniusColimit.stage_mem_essImage_of_descends :
    ∀ (p : ℕ) [Fact p.Prime]
        {X Y : Scheme.{u}} [Y.IsCharP p] [X.IsCharP p]
        (f : X ⟶ Y)
        (G : vectorBundleColimit p Y ⥤ vectorBundleColimit p X)
        [IsStagewisePullback p f G] (E : vectorBundles X)
        (_ : ∃ n : ℕ, ∃ F : Y.Modules, ∃ _ : F.IsFiniteLocallyFree,
          Nonempty
            ((Scheme.Modules.pullback
              (@Scheme.Hom.absoluteFrobeniusPowSource p _ X Y f _ n)).obj
                (ULift.down E).obj ≅
              (Scheme.Modules.pullback f).obj F)),
      G.essImage ((stage p X 0).obj E))

end AlgebraicGeometry.Scheme.FrobeniusColimit
