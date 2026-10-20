module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AdicStarLocalMorphismProperty
import StacksCheckRecall

/-!
# Local tests of morphism properties of locally adic-star formal algebraic spaces

The three locality axioms for adic-star ring maps give equivalent tests on
universal affine étale charts, target covers, and source covers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop)
variable (f : X ⟶ Y)

#check (TopologicalRing.IsAdicStarRing.IsLocalMorphismProperty :
  (∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop) → Prop)

variable [IsLocallyAdicStar X] [IsLocallyAdicStar Y]

/- Remark 87.21.4 (Variant for adic-star): the three local tests are equivalent
for a local property of morphisms of WAdm^{adic*}. -/
@[stacks 0ANH] #check (AlgebraicGeometry.IsLocallyAdicStar.tfae P f :
  ChosenBigSite.IsSizeClosed 𝒮 → IsAdicStarRing.IsLocalMorphismProperty P →
    List.TFAE [IsLocallyAdicStar.etaleAffineLocally P f,
      IsLocallyAdicStar.existsCoverOnTarget P f,
      IsLocallyAdicStar.existsCoverOnSource P f])

#check (AlgebraicGeometry.IsLocallyAdicStar.etaleAffineLocally_iff_existsCoverOnTarget P f :
  ChosenBigSite.IsSizeClosed 𝒮 → IsAdicStarRing.IsLocalMorphismProperty P →
    (IsLocallyAdicStar.etaleAffineLocally P f ↔
      IsLocallyAdicStar.existsCoverOnTarget P f))

#check (AlgebraicGeometry.IsLocallyAdicStar.etaleAffineLocally_iff_existsCoverOnSource P f :
  ChosenBigSite.IsSizeClosed 𝒮 → IsAdicStarRing.IsLocalMorphismProperty P →
    (IsLocallyAdicStar.etaleAffineLocally P f ↔
      IsLocallyAdicStar.existsCoverOnSource P f))
