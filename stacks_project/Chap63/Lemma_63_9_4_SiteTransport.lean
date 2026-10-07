module

public import stacks_project.Chap63.Lemma_63_9_4_Transport

@[expose] public section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section
universe u v w

namespace AlgebraicGeometry.Scheme.Etale

/-- The small-etale equivalence uses pullback along the given isomorphism and its inverse. -/
def smallEtaleAmbientEquivalence {T T' : Scheme.{u}} (e : T' ≅ T) : T.Etale ≌ T'.Etale :=
  CategoryTheory.Equivalence.mk (smallEtalePullback e.hom) (smallEtalePullback e.inv)
    ((smallEtalePullbackCompIso e.inv e.hom ≪≫
      eqToIso (congrArg smallEtalePullback e.inv_hom_id) ≪≫ smallEtaleIdentityIso T).symm)
    (smallEtalePullbackCompIso e.hom e.inv ≪≫
      eqToIso (congrArg smallEtalePullback e.hom_inv_id) ≪≫ smallEtaleIdentityIso T')

/-- Transfer the given Kan extension through the actual ambient equivalence over the base. -/
theorem smallEtaleAmbient_hasLeftKanExtension
    {Y T T' : Scheme.{u}} (p : T ⟶ Y) (p' : T' ⟶ Y)
    (e : T' ≅ T) (hp : e.hom ≫ p = p')
    {A : Type v} [Category.{w} A] (F : Y.Etaleᵒᵖ ⥤ A)
    [(smallEtalePullback p).op.HasLeftKanExtension F] :
    (smallEtalePullback p').op.HasLeftKanExtension F := by
  -- Local instance justification (proof-local temporary data): Use the explicitly constructed small-etale equivalence of this fixed e, whose inverse is pullback along e.inv.
  letI : (smallEtalePullback e.hom).IsEquivalence :=
    (smallEtaleAmbientEquivalence e).isEquivalence_functor
  let comparison : smallEtalePullback p ⋙ smallEtalePullback e.hom ≅ smallEtalePullback p' :=
    smallEtalePullbackCompIso e.hom p ≪≫ eqToIso (congrArg smallEtalePullback hp)
  let comparisonOp : (smallEtalePullback p).op ⋙ (smallEtalePullback e.hom).op ≅
      (smallEtalePullback p').op :=
    (Functor.opComp (smallEtalePullback p) (smallEtalePullback e.hom)).symm ≪≫
      NatIso.op comparison.symm
  exact (Functor.hasLeftExtension_iff_postcomp₁ comparisonOp F).2 inferInstance

end AlgebraicGeometry.Scheme.Etale
end
