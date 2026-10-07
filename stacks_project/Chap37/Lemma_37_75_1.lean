module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberIntegral.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.75.1: the separable-degree-weighted fibre integral of an
integer-valued function commutes with base change along a cartesian square. -/
@[stacks 0F39] #check (AlgebraicGeometry.Scheme.Hom.fiberIntegral_baseChange :
  ∀ {U U' V V' : Scheme.{u}} (π : U ⟶ V) (h : U' ⟶ U)
      (π' : U' ⟶ V') (g : V' ⟶ V) [LocallyQuasiFinite π]
      [hπ : Filter.TendstoCofinite (fun u : U ↦ π u)]
      (sq : IsPullback h π' π g) (w : U → ℤ),
    (fun v' : V' ↦ π.fiberIntegral hπ w (g v')) =
      π'.fiberIntegral (tendstoCofinite_of_isPullback sq hπ) (fun u' ↦ w (h u')))

end AlgebraicGeometry.Scheme.Hom
