module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalMorphismProperty
public import stacks_project.Chap87.Lemma_87_21_3_Local
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

/- Lemma 87.21.3: For a morphism of locally countably indexed formal
algebraic spaces and a local property of morphisms of `WAdm^count`, universal
testing on affine étale squares, testing on a target cover and covers of its
pullbacks, and testing on a source cover factoring through affine étale target
charts are equivalent. -/
@[stacks 0ANG] #check (AlgebraicGeometry.IsLocallyCountablyIndexed.tfae :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    (hP : IsLocalMorphismProperty P),
    List.TFAE [etaleAffineLocally P f, existsCoverOnTarget P f,
      existsCoverOnSource P f])

#check (AlgebraicGeometry.IsLocallyCountablyIndexed.etaleAffineLocally_iff_existsCoverOnTarget :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    (hP : IsLocalMorphismProperty P),
    etaleAffineLocally P f ↔ existsCoverOnTarget P f)

#check (AlgebraicGeometry.IsLocallyCountablyIndexed.etaleAffineLocally_iff_existsCoverOnSource :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    (hP : IsLocalMorphismProperty P),
    etaleAffineLocally P f ↔ existsCoverOnSource P f)

end AlgebraicGeometry.IsLocallyCountablyIndexed
