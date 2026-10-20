module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffinePresentation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineTypes
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Local countable indexing, adic and Noetherian types of formal algebraic spaces

These properties use representable etale atlases on the same functor-of-points carrier
as the canonical formal-space definition, with the canonical compatible affine presentations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A formal algebraic space over `S` is locally countably indexed when it
admits an étale atlas by countably indexed affine formal algebraic spaces. -/
@[mk_iff]
class IsLocallyCountablyIndexed {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [formalSpace : IsFormalAlgebraicSpace X] : Prop where
  /-- There is an étale atlas by countably indexed affine formal algebraic
  spaces, representable by algebraic spaces and jointly fppf-locally
  surjective. -/
  exists_atlas :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, AffineFormalAlgebraicSpace.IsCountablyIndexedAffine (cover i)) ∧
        (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)

namespace IsLocallyCountablyIndexed

/-- A locally countably indexed formal algebraic space admits an étale atlas by
countably indexed affine formal algebraic spaces. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyCountablyIndexed X] :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, AffineFormalAlgebraicSpace.IsCountablyIndexedAffine (cover i)) ∧
        (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

/-- Locally countably indexed formal algebraic spaces are exactly formal
algebraic spaces with an étale atlas by countably indexed affine charts. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] :
    IsLocallyCountablyIndexed X ↔
      ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, AffineFormalAlgebraicSpace.IsCountablyIndexedAffine (cover i)) ∧
          (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

end IsLocallyCountablyIndexed


/-- A formal algebraic space over `S` is locally adic* when it admits an étale
atlas by adic* affine formal algebraic spaces. -/
@[mk_iff]
class IsLocallyAdicStar {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [formalSpace : IsFormalAlgebraicSpace X] : Prop where
  /-- There is an étale atlas by adic* affine formal algebraic spaces,
  representable by algebraic spaces and jointly fppf-locally surjective. -/
  exists_atlas :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsAdicStarAffine (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)

namespace IsLocallyAdicStar

/-- A locally adic* formal algebraic space admits an étale atlas by adic*
affine formal algebraic spaces. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyAdicStar X] :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsAdicStarAffine (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

/-- Locally adic* formal algebraic spaces are exactly formal algebraic spaces
with an étale atlas by adic* affine charts. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] :
    IsLocallyAdicStar X ↔
      ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, IsAdicStarAffine (cover i)) ∧
          (∀ i, representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

end IsLocallyAdicStar

namespace IsAdicStarAffine

/-- An adic* affine formal algebraic space that is a formal algebraic space is
locally adic*. -/
instance instIsLocallyAdicStar {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsAdicStarAffine X] : IsLocallyAdicStar X :=
  sorry

end IsAdicStarAffine

/-- A formal algebraic space over `S` is locally Noetherian when it admits an
étale atlas by Noetherian affine formal algebraic spaces. -/
@[mk_iff]
class IsLocallyNoetherian {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [formalSpace : IsFormalAlgebraicSpace X] : Prop where
  /-- There is an étale atlas by Noetherian affine formal algebraic spaces,
  representable by algebraic spaces and jointly fppf-locally surjective. -/
  exists_noetherian_atlas :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsNoetherianAffine (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)

namespace IsLocallyNoetherian

/-- The representable functor of a Noetherian affine scheme over `S` is a
locally Noetherian formal algebraic space. -/
instance instYoneda {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] [AlgebraicGeometry.IsNoetherian U.left] :
    IsLocallyNoetherian (yoneda.obj U) :=
  sorry

/-- A locally Noetherian formal algebraic space admits an étale atlas by
Noetherian affine formal algebraic spaces. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsNoetherianAffine (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

/-- Locally Noetherian formal algebraic spaces are exactly formal algebraic
spaces with an étale atlas by Noetherian affine charts. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] :
    IsLocallyNoetherian X ↔
      ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, IsNoetherianAffine (cover i)) ∧
          (∀ i, representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

end IsLocallyNoetherian

namespace IsNoetherianAffine

/-- A Noetherian affine formal algebraic space that is a formal algebraic space
is locally Noetherian. -/
instance instIsLocallyNoetherian {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsNoetherianAffine X] : IsLocallyNoetherian X :=
  sorry

end IsNoetherianAffine

end AlgebraicGeometry.FormalAlgebraicSpace

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine

/-- A countably indexed affine formal algebraic space that is a formal algebraic
space is locally countably indexed. -/
instance instIsLocallyCountablyIndexed {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u)
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace X] [IsCountablyIndexedAffine X] :
    FormalAlgebraicSpace.IsLocallyCountablyIndexed X :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine
