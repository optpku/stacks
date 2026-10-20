module

public import ReasLib.AlgebraicGeometry.HomStack.NonEffective
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.GroupoidsOver AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.HomStack
open scoped CategoryTheory.MonObj

universe u

/- Lemma 110.72.4: the canonical restriction from the mapping-stack fibre over
the power-series spectrum to compatible formal objects over its infinitesimal
truncations is not essentially surjective. -/
@[stacks 0AFB] #check (AlgebraicGeometry.HomStack.not_essSurj_canonicalRestriction :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ¬ IsAlgebraicClosureOfFiniteField k)
    (A0 : SchemeOverField k) [GrpObj A0] [AbelianVariety A0] (hA0 : ¬ IsIso A0.hom)
    (X : Over (specPowerSeries k)) [Projective X.hom] [Flat X.hom]
    (h_connected : ∀ s : specPowerSeries k,
      GeometricallyConnected (X.hom.fiberToSpecResidueField s))
    (h_dim : ∀ s : specPowerSeries k, topologicalKrullDim (X.hom.fiber s) = 1)
    (h_regular : Scheme.Regular X.left)
    (h_loop : IsNodalWithRationalComponentLoop (specialFiber X)),
    ¬ (FormalObject.powerSeriesRestriction
      (homStack X (classifyingTorsors (constantAbelianScheme A0)))).EssSurj)
