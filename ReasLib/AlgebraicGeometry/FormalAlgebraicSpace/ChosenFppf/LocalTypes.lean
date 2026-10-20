module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeConditions
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeLocality

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open CategoryTheory.Functor Opposite
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A formal algebraic space is locally countably indexed when every morphism
from an affine formal algebraic space that is representable by algebraic
spaces and relatively étale has countably indexed source. -/
class IsLocallyCountablyIndexed {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsFormalAlgebraicSpace X where
  /-- Every étale morphism from an affine formal algebraic space
  has countably indexed source. -/
  of_etale_affine :
    ∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
      IsAffineFormalAlgebraicSpace Y → ChosenBigFppfSite.etale f → IsCountablyIndexedAffine Y

namespace IsLocallyCountablyIndexed

/-- A countably indexed affine formal algebraic space is locally countably
indexed. -/
instance ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCountablyIndexedAffine X] : IsLocallyCountablyIndexed X :=
  sorry

/-- A locally countably indexed formal algebraic space has every representable
étale affine chart countably indexed. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsLocallyCountablyIndexed X]
    {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X)
    (hY : IsAffineFormalAlgebraicSpace Y)
    (het : ChosenBigFppfSite.etale f) :
    IsCountablyIndexedAffine Y :=
  sorry

/-- Locally countably indexed unpacks as a formal algebraic space whose affine
étale atlas objects are countably indexed. -/
theorem iff_atlas {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsLocallyCountablyIndexed X ↔
      IsFormalAlgebraicSpace X ∧
        ∃ (ι : Type (max u v))
          (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
            (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
              (∀ i, ChosenBigFppfSite.etale (π i)) ∧
                  Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                    ∀ i, IsCountablyIndexedAffine (X_ i) :=
  sorry

end IsLocallyCountablyIndexed

/-- A formal algebraic space is locally countably indexed and classical when
every morphism from an affine formal algebraic space that is representable by
algebraic spaces and relatively étale has countably indexed and classical
source. -/
class IsLocallyClassical {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsFormalAlgebraicSpace X where
  /-- Every étale morphism from an affine formal algebraic space
  has countably indexed and classical source. -/
  of_etale_affine :
    ∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
      IsAffineFormalAlgebraicSpace Y → ChosenBigFppfSite.etale f → IsCountablyIndexedAffine Y ∧ IsClassicalAffine Y

namespace IsLocallyClassical

/-- A countably indexed classical affine formal algebraic space is locally
countably indexed and classical. -/
instance ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCountablyIndexedAffine X] [IsClassicalAffine X] :
    IsLocallyClassical X :=
  sorry

/-- A locally countably indexed and classical formal algebraic space has every
étale affine chart countably indexed and classical. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsLocallyClassical X]
    {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X)
    (hY : IsAffineFormalAlgebraicSpace Y)
    (het : ChosenBigFppfSite.etale f) :
    IsCountablyIndexedAffine Y ∧ IsClassicalAffine Y :=
  sorry

/-- Locally countably indexed and classical unpacks as a formal algebraic space
whose affine étale atlas objects are countably indexed and classical. -/
theorem iff_atlas {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsLocallyClassical X ↔
      IsFormalAlgebraicSpace X ∧
        ∃ (ι : Type (max u v))
          (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
            (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
              (∀ i, ChosenBigFppfSite.etale (π i)) ∧
                  Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                    ∀ i, IsCountablyIndexedAffine (X_ i) ∧ IsClassicalAffine (X_ i) :=
  sorry

end IsLocallyClassical

namespace IsLocallyCountablyIndexed

/-- A locally countably indexed and classical formal algebraic space is locally
countably indexed. -/
instance of_isLocallyClassical {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsLocallyClassical X] :
    IsLocallyCountablyIndexed X :=
  sorry

end IsLocallyCountablyIndexed

/-- A formal algebraic space is locally weakly adic when every morphism from an
affine formal algebraic space that is representable by algebraic spaces and
relatively étale has weakly adic source. -/
class IsLocallyWeaklyAdic {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsFormalAlgebraicSpace X where
  /-- Every étale morphism from an affine formal algebraic space
  has weakly adic source. -/
  of_etale_affine :
    ∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
      IsAffineFormalAlgebraicSpace Y → ChosenBigFppfSite.etale f → IsWeaklyAdicAffine Y

namespace IsLocallyWeaklyAdic

/-- A weakly adic affine formal algebraic space is locally weakly adic. -/
instance ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsWeaklyAdicAffine X] :
    IsLocallyWeaklyAdic X :=
  sorry

/-- A locally weakly adic formal algebraic space has every étale
affine chart weakly adic. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsLocallyWeaklyAdic X]
    {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X)
    (hY : IsAffineFormalAlgebraicSpace Y)
    (het : ChosenBigFppfSite.etale f) :
    IsWeaklyAdicAffine Y :=
  sorry

/-- Locally weakly adic unpacks as a formal algebraic space whose affine étale
atlas objects are weakly adic. -/
theorem iff_atlas {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsLocallyWeaklyAdic X ↔
      IsFormalAlgebraicSpace X ∧
        ∃ (ι : Type (max u v))
          (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
            (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
              (∀ i, ChosenBigFppfSite.etale (π i)) ∧
                  Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                    ∀ i, IsWeaklyAdicAffine (X_ i) :=
  sorry

end IsLocallyWeaklyAdic

namespace IsFormalAlgebraicSpace

/-- A formal algebraic space is locally Noetherian when every morphism from an
affine formal algebraic space that is representable by algebraic spaces and
relatively étale has Noetherian source. Nested to avoid clashing with the
scheme class `AlgebraicGeometry.IsLocallyNoetherian`. -/
class IsLocallyNoetherian {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsFormalAlgebraicSpace X where
  /-- Every étale morphism from an affine formal algebraic space
  has Noetherian source. -/
  of_etale_affine :
    ∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
      IsAffineFormalAlgebraicSpace Y → ChosenBigFppfSite.etale f → IsNoetherianAffine Y

namespace IsLocallyNoetherian

/-- A Noetherian affine formal algebraic space is locally Noetherian. -/
instance ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsNoetherianAffine X] :
    IsLocallyNoetherian X :=
  sorry

/-- A locally Noetherian formal algebraic space has every étale
affine chart Noetherian. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsLocallyNoetherian X]
    {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X)
    (hY : IsAffineFormalAlgebraicSpace Y)
    (het : ChosenBigFppfSite.etale f) :
    IsNoetherianAffine Y :=
  sorry

/-- Locally Noetherian unpacks as a formal algebraic space whose affine étale
atlas objects are Noetherian. -/
theorem iff_atlas {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsLocallyNoetherian X ↔
      IsFormalAlgebraicSpace X ∧
        ∃ (ι : Type (max u v))
          (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
            (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
              (∀ i, ChosenBigFppfSite.etale (π i)) ∧
                  Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                    ∀ i, IsNoetherianAffine (X_ i) :=
  sorry

end IsLocallyNoetherian

end IsFormalAlgebraicSpace

end AlgebraicGeometry
