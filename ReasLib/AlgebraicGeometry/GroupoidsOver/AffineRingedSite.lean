module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.AssociatedStructureSheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.AffineComparison

/-!
# Structure sheaves on associated affine sites

The canonical structure sheaf of a category fibred in groupoids admits a
universe lift and restricts to a sheaf on each associated affine site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The universe lift of the canonical structure sheaf `𝒪_𝒳` to `RingCat.{u + 1}`. -/
def liftedAssociatedStructureSheaf (X : GroupoidsOver S) (τ : StandardTopology) :
    Sheaf (X.associatedTopology τ) RingCat.{u + 1} :=
  (sheafCompose (X.associatedTopology τ) (Scheme.Site.ringUniverseLift.{u, u + 1})).obj
    (associatedStructureSheaf X τ)

/-- `liftedAssociatedStructureSheaf` is `sheafCompose` of `ringUniverseLift` applied
to the canonical `associatedStructureSheaf`. -/
theorem liftedAssociatedStructureSheaf_eq (X : GroupoidsOver S)
    (τ : StandardTopology) :
    liftedAssociatedStructureSheaf X τ =
      (sheafCompose (X.associatedTopology τ)
          (Scheme.Site.ringUniverseLift.{u, u + 1})).obj
        (associatedStructureSheaf X τ) :=
  sorry

/-- Componentwise, the lifted sheaf is the `ULift` of the canonical sections of
`𝒪_𝒳`. -/
theorem liftedAssociatedStructureSheaf_obj {X : GroupoidsOver S}
    (τ : StandardTopology) (x : X.total) :
    (liftedAssociatedStructureSheaf X τ).obj.obj (op x) =
      Scheme.Site.ringUniverseLiftObj.{u, u + 1}
        ((associatedStructureSheaf X τ).obj.obj (op x)) :=
  sorry

/-- The lifted structure sheaf at an object over `U` has value the universe lift
of the global-section ring `Γ(U, 𝒪_U)`. -/
theorem liftedAssociatedStructureSheaf_obj_globalSections {X : GroupoidsOver S}
    (τ : StandardTopology) (x : X.total) :
    (liftedAssociatedStructureSheaf X τ).obj.obj (op x) =
      Scheme.Site.ringUniverseLiftObj.{u, u + 1}
        (RingCat.of Γ((X.p.obj x).left, ⊤)) :=
  sorry

/-- The associated `τ`-site of `X`, ringed by the universe-lifted structure sheaf. -/
abbrev liftedAssociatedRingedSite (X : GroupoidsOver S) (τ : StandardTopology) :
    RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf (X.associatedTopology τ)
    (liftedAssociatedStructureSheaf X τ)

/-- The structure sheaf of `liftedAssociatedRingedSite X τ` is
`liftedAssociatedStructureSheaf X τ`. -/
theorem liftedAssociatedRingedSite_structureSheaf (X : GroupoidsOver S)
    (τ : StandardTopology) :
    (liftedAssociatedRingedSite X τ).structureSheaf =
      liftedAssociatedStructureSheaf X τ :=
  sorry

/-- The restriction `𝒪` of the lifted structure sheaf `𝒪_𝒳` along
`affineInclusion X`, as a sheaf on the associated affine `τ`-site. -/
def associatedAffineStructureSheaf (X : GroupoidsOver S) (τ : StandardTopology) :
    Sheaf (X.associatedAffineTopology τ) RingCat.{u + 1} :=
  ((affineInclusion X).sheafPushforwardContinuous RingCat.{u + 1}
      (X.associatedAffineTopology τ) (X.associatedTopology τ)).obj
    (liftedAssociatedStructureSheaf X τ)

/-- `associatedAffineStructureSheaf` is continuous pushforward of
`liftedAssociatedStructureSheaf` along the affine inclusion. -/
theorem associatedAffineStructureSheaf_eq (X : GroupoidsOver S)
    (τ : StandardTopology) :
    associatedAffineStructureSheaf X τ =
      ((affineInclusion X).sheafPushforwardContinuous RingCat.{u + 1}
          (X.associatedAffineTopology τ) (X.associatedTopology τ)).obj
        (liftedAssociatedStructureSheaf X τ) :=
  sorry

/-- The restriction of `𝒪_𝒳` to `𝒳_affine` is a sheaf for every associated
affine `τ`-topology. -/
theorem associatedAffineStructureSheaf_isSheaf (X : GroupoidsOver S)
    (τ : StandardTopology) :
    Presheaf.IsSheaf (X.associatedAffineTopology τ)
      (associatedAffineStructureSheaf X τ).obj :=
  sorry

/-- On an affine object `x`, the restricted structure sheaf agrees with the
lifted value of `𝒪_𝒳` at `x`. -/
theorem associatedAffineStructureSheaf_obj (X : GroupoidsOver S)
    (τ : StandardTopology) (x : Affine X) :
    (associatedAffineStructureSheaf X τ).obj.obj (op x) =
      (liftedAssociatedStructureSheaf X τ).obj.obj (op x.obj) :=
  sorry

/-- Unfolding of the restricted structure sheaf as precomposition along
`affineInclusion`. -/
def associatedAffineStructureSheafToPushforward (X : GroupoidsOver S)
    (τ : StandardTopology) :
    (associatedAffineStructureSheaf X τ).obj ≅
      (affineInclusion X).op ⋙ (liftedAssociatedStructureSheaf X τ).obj :=
  ((affineInclusion X).sheafPushforwardContinuousCompSheafToPresheafIso
      RingCat.{u + 1} (X.associatedAffineTopology τ) (X.associatedTopology τ)).app
    (liftedAssociatedStructureSheaf X τ)

/-- `associatedAffineStructureSheafToPushforward` is the continuous-pushforward
identification of underlying presheaves. -/
theorem associatedAffineStructureSheafToPushforward_eq (X : GroupoidsOver S)
    (τ : StandardTopology) :
    associatedAffineStructureSheafToPushforward X τ =
      ((affineInclusion X).sheafPushforwardContinuousCompSheafToPresheafIso
          RingCat.{u + 1} (X.associatedAffineTopology τ)
          (X.associatedTopology τ)).app
        (liftedAssociatedStructureSheaf X τ) :=
  sorry

/-- The associated affine `τ`-site of `X`, ringed by the restriction of `𝒪_𝒳`. -/
abbrev associatedAffineRingedSite (X : GroupoidsOver S) (τ : StandardTopology) :
    RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf (X.associatedAffineTopology τ)
    (associatedAffineStructureSheaf X τ)

/-- The structure sheaf of `associatedAffineRingedSite X τ` is
`associatedAffineStructureSheaf X τ`. -/
theorem associatedAffineRingedSite_structureSheaf (X : GroupoidsOver S)
    (τ : StandardTopology) :
    (associatedAffineRingedSite X τ).structureSheaf =
      associatedAffineStructureSheaf X τ :=
  sorry

/-- The affine inclusion as a functor of the associated ringed sites. -/
abbrev affineInclusionRinged (X : GroupoidsOver S) (τ : StandardTopology) :
    (associatedAffineRingedSite X τ).carrier ⥤
      (liftedAssociatedRingedSite X τ).carrier :=
  affineInclusion X

/-- On objects, `affineInclusionRinged` is the underlying affine inclusion. -/
theorem affineInclusionRinged_obj (X : GroupoidsOver S) (τ : StandardTopology)
    (x : Affine X) :
    (affineInclusionRinged X τ).obj x = (affineInclusion X).obj x :=
  sorry

end AlgebraicGeometry.GroupoidsOver
