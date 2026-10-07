module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries.Inseparable

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

/- Lemma 53.13.8: a linear series on a smooth proper curve in characteristic `p > 0`
either contains a pencil whose associated morphism to the projective line is generically
étale, or admits a linear series of degree at most `d / p` on the first Frobenius twist. -/
@[stacks 0CD3] #check
  (AlgebraicGeometry.LinearSeries.existsGenericallyEtaleOrFrobeniusTwist :
    ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (X : SchemeOverField k) [Curve X] [IsProper X.hom] [Smooth X.hom]
    {d r : ℕ}
    (g : LinearSeries X (topologicalKrullDim_eq_one X).le d r) (hr : 1 ≤ r),
    (∃ (g1 : LinearSeries X (topologicalKrullDim_eq_one X).le d 1)
        (W : Submodule k (Scheme.Hom.globalSectionsMod X.hom g.lineBundle))
        (hW_sub : W ≤ g.sections)
        (hW_dim : Module.finrank k W = 2)
        (hlineBundle : g1.lineBundle = g.lineBundle)
        (hsections : hlineBundle ▸ g1.sections = W)
        (b : Module.Basis (Fin 2) k g1.sections)
        (φ : X ⟶ Over.mk (ProjectiveSpace.toSpec k 1))
        (α : (Scheme.Modules.pullback φ.left).obj
          (ProjectiveSpace.twistingSheaf k 1 1) ⟶ g1.lineBundle),
        (∀ i : Fin 2,
          SheafOfModules.sectionsMap α
              (Scheme.Modules.sectionsPullback φ.left
                (ProjectiveSpace.twistingSheaf k 1 1)
                (ProjectiveSpace.coordinateTwistSection k 1 i)) =
            RingedSpace.sectionFromTop g1.lineBundle (g1.inclusion (b i))) ∧
          ∃ U : X.left.Opens, Nonempty U ∧
            Etale (φ.left.resLE ⊤ U le_top ≫
              Iso.hom (topIso (Over.mk (ProjectiveSpace.toSpec k 1)).left))) ∨
      ∃ (d' : ℕ)
        (h_curve : Curve (Scheme.pPowerTwist (p := p) X.hom 1))
        (h_proper : IsProper (Scheme.pPowerTwist (p := p) X.hom 1).hom)
        (g' : @LinearSeries k _ (Scheme.pPowerTwist (p := p) X.hom 1)
          h_proper h_curve.topologicalKrullDim_eq_one.le d' r),
        d' ≤ d / p)
