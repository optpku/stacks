module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules.IsPureAlong

/- Lemma 38.18.2: under the stated finite-type, flatness, étaleness, purity, and
associated-point coverage hypotheses, purity along `X_s` is equivalent to every relative
associated point after the elementary étale base change that lies over a specialization of
the selected point belonging to the image of the canonical comparison morphism. -/
@[stacks 05L4] #check
  (AlgebraicGeometry.Scheme.Modules.IsPureAlong.iff_relativeAssassin_subset_range :
    ∀ {X S X' : Scheme.{u}} (f : X ⟶ S)
      [Scheme.Hom.FiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      (s : S) (U : Scheme.EtaleNeighborhood S s) (hU : U.IsElementary)
      (g : X' ⟶ X) [Etale g] (f' : X' ⟶ U.toEtale.left) [Scheme.Hom.FiniteType f']
      (sq : CommSq f' g U.toEtale.hom f)
      (hflat : ∀ x : f.fiber s, flatOverAt ℱ f (f.fiberι s x))
      (hpure : ((Scheme.Modules.pullback g).obj ℱ).IsPureAlong f' U.point)
      (hass : ((Scheme.Modules.pullback (f.fiberι s)).obj ℱ).associatedPoints ⊆
        (f.fiberι s) ⁻¹' Set.range g),
      ℱ.IsPureAlong f s ↔
        relativeAssassin (pullback.snd f U.toEtale.hom)
            ((Scheme.Modules.pullback (pullback.fst f U.toEtale.hom)).obj ℱ) ∩
          (pullback.snd f U.toEtale.hom) ⁻¹' {t | t ⤳ U.point} ⊆
            Set.range (pullback.lift g f' sq.w.symm))

end Scheme.Modules.IsPureAlong
end AlgebraicGeometry
