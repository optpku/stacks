/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.Nodal.DVR
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 55.14.2 -/
@[stacks 0CDD] #check (AlgebraicGeometry.Scheme.Hom.exists_etale_nodal_model_over_dvr : ∀
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [AtWorstNodal f]
    (x : X) (hx : f x = IsLocalRing.closedPoint R),
    ∃ (R' : Type u) (h_commR' : CommRing R') (h_domainR' : IsDomain R')
      (h_dvrR' : IsDiscreteValuationRing R') (h_algebra : Algebra R R')
      (h_extension : IsExtensionOfDiscreteValuationRings R R')
      (h_etale : Algebra.Etale R R')
      (pi : R') (hpi : Irreducible pi) (A : CommAlgCat R') (U : Scheme.{u})
      (uX : U ⟶ X) (uR : U ⟶ Spec (CommRingCat.of R'))
      (uA : U ⟶ Spec (CommRingCat.of A)) (x' : U),
      (A = CommAlgCat.of R'
          (MvPolynomial (Fin 2) R' ⧸ Ideal.span
            ({MvPolynomial.X 0 * MvPolynomial.X 1} :
              Set (MvPolynomial (Fin 2) R'))) ∨
        ∃ n : ℕ, A = CommAlgCat.of R' (NodalModel.Power.Ring R' pi n)) ∧
        Etale uX ∧ Etale uA ∧
          uX ≫ f = uR ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) ∧
            uA ≫ Spec.map (CommRingCat.ofHom (algebraMap R' A)) = uR ∧
              uX x' = x)
