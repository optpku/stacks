module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Separation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Pullback
public import ReasLib.AlgebraicGeometry.FormalSpectrum.Pullback
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.AffineFormalAlgebraicSpace

universe u v

/- Lemma 87.16.4 (1). -/
@[stacks 0AN3] #check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.instPullback :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    [IsSeparatedFormalAlgebraicSpace Z],
    IsAffineFormalAlgebraicSpace (pullback f g))

/- Lemma 87.16.4 (2). -/
@[stacks 0AN3] #check (AlgebraicGeometry.IsMcQuillan.instPullback :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsMcQuillan X] [IsMcQuillan Y]
    [IsSeparatedFormalAlgebraicSpace Z],
    IsMcQuillan (pullback f g))

/- Lemma 87.16.4 (3). -/
@[stacks 0AN3] #check (AlgebraicGeometry.AffineFormalAlgebraicSpace.pullback_spfMap_iso_spfCompleted :
    ∀ {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    [TopologicalRing.IsWeaklyAdmissibleRing B]
    [TopologicalRing.IsWeaklyAdmissibleRing C]
    [Algebra C A] [Algebra C B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (hC : Spec (.of C) ⟶ S)
    (hφA : Continuous (algebraMap C A)) (hφB : Continuous (algebraMap C B))
    (hA_over : Spec.map (CommRingCat.ofHom (algebraMap C A)) ≫ hC = hA)
    (hB_over : Spec.map (CommRingCat.ofHom (algebraMap C B)) ≫ hC = hB)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    [HasPullbacks (Sheaf (Scheme.fppfTopology.over S) (Type u))],
    ∃ e : pullback (spfMap (algebraMap C A) hφA hA_over)
        (spfMap (algebraMap C B) hφB hB_over) ≅ spfCompleted hC hφA hφB,
      e.hom ≫ spfCompletedFst hA hC hφA hφB hA_over =
        pullback.fst (spfMap (algebraMap C A) hφA hA_over)
          (spfMap (algebraMap C B) hφB hB_over) ∧
      e.hom ≫ spfCompletedSnd hB hC hφA hφB hB_over =
        pullback.snd (spfMap (algebraMap C A) hφA hA_over)
          (spfMap (algebraMap C B) hφB hB_over))
