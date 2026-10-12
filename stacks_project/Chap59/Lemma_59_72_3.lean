/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Decomposition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom

universe u

/- Lemma 59.72.3 (1): after a surjective affine base change, a quasi-finite finitely
presented morphism of affine schemes contains a thickening that is finite etale over the
new base. -/
@[stacks 095K] #check (@AlgebraicGeometry.Scheme.Hom.exists_surjective_affine_baseChange_finiteEtale_thickening :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffine X] [IsAffine Y]
      [QuasiFinite f] [FinitePresentation f],
      ∃ (X' Z' : Scheme.{u}) (g : X' ⟶ X) (i : Z' ⟶ pullback g f),
        IsAffine X' ∧ Surjective g ∧ IsThickening i ∧
          IsFinite (i ≫ pullback.fst g f) ∧ Etale (i ≫ pullback.fst g f))

/- Lemma 59.72.3 (2): a quasi-finite finitely presented morphism of affine schemes admits
a finite stratification by affine constructible locally closed subschemes and finite locally
free surjective covers on which the reduced base change is a finite coproduct of the reduced
base. -/
@[stacks 095K] #check (@AlgebraicGeometry.Scheme.Hom.exists_finiteAffineStratification_reduction_iso_coproduct :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffine X] [IsAffine Y]
      [QuasiFinite f] [FinitePresentation f],
      ∃ (S : Scheme.Stratification X) (_ : Finite S.index)
        (_ : ∀ i, Topology.IsConstructible (Set.range (S.ι i).base))
        (_ : ∀ i, IsAffine (S.stratum i))
        (X' : S.index → Scheme.{u}) (g : ∀ i, X' i ⟶ S.stratum i)
        (_ : ∀ i, Surjective (g i))
        (_ : ∀ i, IsFiniteLocallyFree (g i)) (n : S.index → ℕ)
        (e : ∀ i, Scheme.reduction (pullback (g i ≫ S.ι i) f) ≅
          ∐ fun _ : Fin (n i) ↦ Scheme.reduction (X' i)),
        ∀ i, Scheme.reductionMap (pullback.fst (g i ≫ S.ι i) f) =
          (e i).hom ≫ Sigma.desc (fun _ : Fin (n i) ↦
            𝟙 (Scheme.reduction (X' i))))
