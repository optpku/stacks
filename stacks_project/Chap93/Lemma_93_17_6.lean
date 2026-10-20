module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Smoothing

/-!
# Projective flat smoothings of proper lci curves with isolated singularities
-/

@[expose]
public section

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 93.17.6: Let `X` be a scheme over a field `k`. Assume `X` is proper over `k`,
`X` is a local complete intersection over `k`, `X` has dimension `≤ 1`, and
`X ⟶ Spec k` is smooth except at finitely many points. Then there exists a flat
projective morphism `Y ⟶ Spec (PowerSeries k)` (that is, `Spec k[[t]]`) whose
generic fibre is smooth and whose special fibre is isomorphic to `X` as a
`k`-scheme. Here the generic fibre is the fibre over
`genericPoint (Spec (PowerSeries k))`, and the special fibre is the pullback of
`Y` along `Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff)`. -/
@[stacks 0E7Y]
#check (AlgebraicGeometry.SchemeOverField.exists_flat_projective_smoothing :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [IsLocalCompleteIntersectionOver k X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hns : {x : X.left | ¬ X.hom.SmoothAt x}.Finite),
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of (PowerSeries k)))
      (_ : Projective f) (_ : Flat f)
      (e : Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff))) ≅ X),
      Smooth (f.fiberToSpecResidueField
        (genericPoint (Spec (CommRingCat.of (PowerSeries k))))))

end AlgebraicGeometry.SchemeOverField
