module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.Etale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleSite.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.RestrictionTopos

/-!
# Small étale sites and topoi of formal algebraic spaces

Explicit reductions identify the small étale sites with those of algebraic spaces.
Arbitrary morphisms induce base change and morphisms of étale topoi.
Étale morphisms act by postcomposition along their induced morphisms of reductions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.ReductionData

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]

/-- Base change on the spaces-étale sites along the induced morphism of reductions. -/
abbrev spacesEtalePullback (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    spacesEtaleSite RY ⥤ spacesEtaleSite RX :=
  AlgebraicSpace.spacesEtalePullback (map RX RY f)

/-- Base change on the spaces-étale sites is algebraic-space base change on reductions. -/
theorem spacesEtalePullback_eq (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    spacesEtalePullback RX RY f = AlgebraicSpace.spacesEtalePullback (map RX RY f) :=
  rfl

/-- Base change on the spaces-étale sites is continuous. -/
theorem spacesEtalePullback_isContinuous
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    (spacesEtalePullback RX RY f).IsContinuous
      (spacesEtaleTopology RY) (spacesEtaleTopology RX) :=
  AlgebraicSpace.spacesEtalePullback_isContinuous (map RX RY f)

/-- Base change on the spaces-étale sites induces a morphism of sites. -/
theorem spacesEtalePullback_isMorphismOfSites
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    IsMorphismOfSites (spacesEtaleTopology RY) (spacesEtaleTopology RX)
      (spacesEtalePullback RX RY f) :=
  AlgebraicSpace.spacesEtalePullback_isMorphismOfSites (map RX RY f)

/-- The morphism of spaces-étale topoi induced by the morphism of reductions. -/
abbrev spacesEtaleMorphismOfTopoi
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    MorphismOfTopoiIn (spacesEtaleTopology RY) (spacesEtaleTopology RX) :=
  AlgebraicSpace.spacesEtaleMorphismOfTopoi (map RX RY f)

/-- The spaces-étale topos morphism is the topos morphism of the induced reduction map. -/
theorem spacesEtaleMorphismOfTopoi_eq
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    spacesEtaleMorphismOfTopoi RX RY f =
      AlgebraicSpace.spacesEtaleMorphismOfTopoi (map RX RY f) :=
  rfl

/-- Postcomposition along the induced étale morphism of reductions. -/
def etaleRestriction (RX : ReductionData X) (RY : ReductionData Y)
    (f : X ⟶ Y) [Etale f] :
    AlgebraicSpace.smallEtaleSite RX.space ⥤ AlgebraicSpace.smallEtaleSite RY.space :=
  @AlgebraicSpace.etaleRestriction S RX.space RY.space (map RX RY f)
    (map_etale RX RY f)

/-- Restriction on the small étale sites is postcomposition on reductions. -/
theorem etaleRestriction_def (RX : ReductionData X) (RY : ReductionData Y)
    (f : X ⟶ Y) [Etale f] :
    etaleRestriction RX RY f =
      @AlgebraicSpace.etaleRestriction S RX.space RY.space (map RX RY f)
        (map_etale RX RY f) :=
  rfl

/-- Postcomposition along an étale morphism of formal algebraic spaces is cocontinuous. -/
theorem etaleRestriction_isCocontinuous (RX : ReductionData X) (RY : ReductionData Y)
    (f : X ⟶ Y) [Etale f] :
    (etaleRestriction RX RY f).IsCocontinuous
      (AlgebraicSpace.smallEtaleTopology RX.space)
      (AlgebraicSpace.smallEtaleTopology RY.space) :=
  @AlgebraicSpace.etaleRestriction_isCocontinuous S RX.space RY.space
    (map RX RY f) (map_etale RX RY f)

/-- Postcomposition along an étale morphism of formal algebraic spaces is continuous. -/
theorem etaleRestriction_isContinuous (RX : ReductionData X) (RY : ReductionData Y)
    (f : X ⟶ Y) [Etale f] :
    (etaleRestriction RX RY f).IsContinuous
      (AlgebraicSpace.smallEtaleTopology RX.space)
      (AlgebraicSpace.smallEtaleTopology RY.space) :=
  @AlgebraicSpace.etaleRestriction_isContinuous S RX.space RY.space
    (map RX RY f) (map_etale RX RY f)

/-- The canonical morphism of small étale topoi induced on reductions. -/
abbrev smallEtaleMorphismOfTopoi (RX : ReductionData X) (RY : ReductionData Y)
    (f : X ⟶ Y) :=
  AlgebraicSpace.smallEtaleMorphismOfTopoi (map RX RY f)

/-- The small étale topos morphism is the canonical morphism of the induced reduction map. -/
theorem smallEtaleMorphismOfTopoi_def (RX : ReductionData X) (RY : ReductionData Y)
    (f : X ⟶ Y) :
    smallEtaleMorphismOfTopoi RX RY f =
      AlgebraicSpace.smallEtaleMorphismOfTopoi (map RX RY f) :=
  rfl

/-- Inverse image of the canonical small étale topos morphism is naturally isomorphic
to cocontinuous sheaf pullback along postcomposition. -/
def smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) [Etale f] :
    (smallEtaleMorphismOfTopoi RX RY f).inverseImage ≅
      (etaleRestriction RX RY f).sheafPullbackCocontinuous (Type (u + 1))
        (AlgebraicSpace.smallEtaleTopology RX.space)
        (AlgebraicSpace.smallEtaleTopology RY.space) :=
  @AlgebraicSpace.smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous
    S RX.space RY.space (map RX RY f) (map_etale RX RY f)

/-- The inverse-image comparison is the canonical comparison for the induced reduction map. -/
theorem smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous_spec
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) [Etale f] :
    smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous RX RY f =
      @AlgebraicSpace.smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous
        S RX.space RY.space (map RX RY f) (map_etale RX RY f) :=
  rfl

variable {Z : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace Z]

/-- Base change along a composite is naturally isomorphic to successive base change. -/
def spacesEtalePullbackComp
    (RX : ReductionData X) (RY : ReductionData Y) (RZ : ReductionData Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    spacesEtalePullback RX RZ (f ≫ g) ≅
      spacesEtalePullback RY RZ g ⋙ spacesEtalePullback RX RY f :=
  eqToIso (congrArg AlgebraicSpace.spacesEtalePullback (map_comp RX RY RZ f g)) ≪≫
    AlgebraicSpace.spacesEtalePullbackComp (map RX RY f) (map RY RZ g)

/-- The base-change comparison transports reduction-map composition before comparing pullbacks. -/
theorem spacesEtalePullbackComp_eq
    (RX : ReductionData X) (RY : ReductionData Y) (RZ : ReductionData Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    spacesEtalePullbackComp RX RY RZ f g =
      eqToIso (congrArg AlgebraicSpace.spacesEtalePullback (map_comp RX RY RZ f g)) ≪≫
        AlgebraicSpace.spacesEtalePullbackComp (map RX RY f) (map RY RZ g) :=
  rfl

/-- Inverse images on spaces-étale topoi preserve composition up to natural isomorphism. -/
def spacesEtaleMorphismOfTopoiComp
    (RX : ReductionData X) (RY : ReductionData Y) (RZ : ReductionData Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesEtaleMorphismOfTopoi RX RZ (f ≫ g)).inverseImage ≅
      ((spacesEtaleMorphismOfTopoi RY RZ g).comp
        (spacesEtaleMorphismOfTopoi RX RY f)).inverseImage :=
  eqToIso (congrArg (fun h : RX.space ⟶ RZ.space =>
    (AlgebraicSpace.spacesEtaleMorphismOfTopoi h).inverseImage)
      (map_comp RX RY RZ f g)) ≪≫
    AlgebraicSpace.spacesEtaleMorphismOfTopoiComp (map RX RY f) (map RY RZ g)

/-- The spaces-étale inverse-image comparison is transported from the comparison on reductions. -/
theorem spacesEtaleMorphismOfTopoiComp_eq
    (RX : ReductionData X) (RY : ReductionData Y) (RZ : ReductionData Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    spacesEtaleMorphismOfTopoiComp RX RY RZ f g =
      eqToIso (congrArg (fun h : RX.space ⟶ RZ.space =>
        (AlgebraicSpace.spacesEtaleMorphismOfTopoi h).inverseImage)
          (map_comp RX RY RZ f g)) ≪≫
        AlgebraicSpace.spacesEtaleMorphismOfTopoiComp (map RX RY f) (map RY RZ g) :=
  rfl

/-- Inverse images on small étale topoi preserve composition up to natural isomorphism. -/
def smallEtaleMorphismOfTopoiComp
    (RX : ReductionData X) (RY : ReductionData Y) (RZ : ReductionData Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleMorphismOfTopoi RX RZ (f ≫ g)).inverseImage ≅
      ((smallEtaleMorphismOfTopoi RY RZ g).comp
        (smallEtaleMorphismOfTopoi RX RY f)).inverseImage :=
  eqToIso (congrArg (fun h : RX.space ⟶ RZ.space =>
    (AlgebraicSpace.smallEtaleMorphismOfTopoi h).inverseImage)
      (map_comp RX RY RZ f g)) ≪≫
    AlgebraicSpace.smallEtaleMorphismOfTopoiComp (map RX RY f) (map RY RZ g)

/-- The small étale inverse-image comparison is transported from the comparison on reductions. -/
theorem smallEtaleMorphismOfTopoiComp_eq
    (RX : ReductionData X) (RY : ReductionData Y) (RZ : ReductionData Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleMorphismOfTopoiComp RX RY RZ f g =
      eqToIso (congrArg (fun h : RX.space ⟶ RZ.space =>
        (AlgebraicSpace.smallEtaleMorphismOfTopoi h).inverseImage)
          (map_comp RX RY RZ f g)) ≪≫
        AlgebraicSpace.smallEtaleMorphismOfTopoiComp (map RX RY f) (map RY RZ g) :=
  rfl

end AlgebraicGeometry.FormalAlgebraicSpace.ReductionData
