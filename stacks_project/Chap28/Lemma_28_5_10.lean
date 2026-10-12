/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Topology.DiscreteValuation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 28.5.10 (1): a specialization in a locally Noetherian scheme is realized by the generic
and closed points of the spectrum of a discrete valuation ring. -/
@[stacks 054F] #check (_root_.Specializes.exists_discreteValuationRing_morphism :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] {x' x : X} (h : x' ⤳ x),
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
      (_ : IsDiscreteValuationRing R) (f : Spec (CommRingCat.of R) ⟶ X),
      f (genericPoint (Spec (CommRingCat.of R))) = x' ∧
        f (IsLocalRing.closedPoint R) = x)

/- Lemma 28.5.10 (2): for a nontrivial specialization, the realizing DVR can be chosen inside a
prescribed finite-type extension of the residue field of the general point. -/
@[stacks 054F] #check (
  _root_.Specializes.exists_discreteValuationRing_morphism_with_prescribed_fractionField :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] {x' x : X}
      (h : x' ⤳ x) (hneq : x ≠ x') (K : Type u) [Field K]
      [Algebra (X.residueField x') K] [Algebra.FiniteType (X.residueField x') K],
      ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
        (_ : IsDiscreteValuationRing R) (_ : Algebra R K) (_ : IsFractionRing R K)
        (f : Spec (CommRingCat.of R) ⟶ X),
        f (genericPoint (Spec (CommRingCat.of R))) = x' ∧
          f (IsLocalRing.closedPoint R) = x ∧
          CommSq
            (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x') K)))
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
            (X.fromSpecResidueField x') f)
