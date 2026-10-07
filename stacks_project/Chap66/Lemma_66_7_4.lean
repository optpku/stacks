module

public import stacks_project.Chap66.Lemma_66_7_4_EtaleLocal

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.7.4 (1): let `P` be an étale-local property of scheme germs, let `S` be a scheme,
let `X` be an algebraic space over `S`, and let `x` be a point of `X`. Then `P` holds at every
étale scheme chart through `x` if and only if it holds at some étale scheme chart through `x`. -/
@[stacks 04N2]
theorem forallEtaleAt_iff_existsEtaleAt {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsEtaleLocal) (X : AlgebraicSpace S) (x : Points X) :
    forallEtaleAt P X x ↔ existsEtaleAt P X x :=
  sorry

/-- Lemma 66.7.4 (2): if `X` is representable by a scheme `T` over `S`, then the existence of an
étale scheme chart through the image of `x` with property `P` is equivalent to `P` at
`(T.left, x)`. -/
@[stacks 04N2]
theorem existsEtaleAt_ofOver {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsEtaleLocal) (T : Over S) (x : T.left) :
    existsEtaleAt P (ofOver T) (ofOver.pointsEquiv T x) ↔ P T.left x :=
  sorry

/-- If `T` is a scheme over `S`, then every étale scheme chart of `ofOver T` through the image of
`x` has property `P` if and only if `P` holds at `(T.left, x)`. -/
theorem forallEtaleAt_ofOver {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsEtaleLocal) (T : Over S) (x : T.left) :
    forallEtaleAt P (ofOver T) (ofOver.pointsEquiv T x) ↔ P T.left x :=
  sorry

/-- The étale-local germ criterion at a point transports along an isomorphism to a representable
algebraic space. -/
theorem existsEtaleAt_iso {S : Scheme.{u}} (P : GermProperty.{u}) (hP : P.IsEtaleLocal)
    {X : AlgebraicSpace S} {T : Over S} (e : X ≅ ofOver T) (x : Points X) :
    existsEtaleAt P X x ↔
      P T.left ((ofOver.pointsEquiv T).symm (Points.map e.hom x)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
