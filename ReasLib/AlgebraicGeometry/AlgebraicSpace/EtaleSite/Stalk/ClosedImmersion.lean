module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage

/-!
# Stalk comparison for a closed immersion of algebraic spaces

Evaluation on represented pullbacks of étale neighborhoods defines the canonical map
from a direct-image stalk to the original stalk.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace GeometricPoint

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]

set_option backward.privateInPublic true in
private abbrev closedImmersionRepresentable : yoneda.relativelyRepresentable i :=
  (IsClosedImmersion.presheaf (f := i)).1

set_option backward.privateInPublic true in
/-- The projection from the represented pullback of an étale chart is étale. -/
private theorem closedImmersionPullbackChart_etale (U : smallEtaleSite X) :
    AlgebraicGeometry.AlgebraicSpace.Etale
      (X := ofOver ((closedImmersionRepresentable i).pullback U.hom)) (Y := Z)
      ((closedImmersionRepresentable i).fst U.hom) := sorry

set_option backward.privateInPublic true in
private def closedImmersionPullbackChart (U : smallEtaleSite X) : smallEtaleSite Z :=
  smallEtaleSite.mk ((closedImmersionRepresentable i).fst U.hom)
    (closedImmersionPullbackChart_etale i U)

set_option backward.privateInPublic true in
private def closedImmersionPullbackLift (zbar : GeometricPoint Z)
    (N : SmallEtaleNeighborhood (zbar.map i)) :
    Over.mk zbar.structureHom ⟶ (closedImmersionPullbackChart i N.toSite).left :=
  (closedImmersionRepresentable i).lift zbar.hom N.overHom
    (SmallEtaleNeighborhood.lift_fac N).symm

set_option backward.privateInPublic true in
/-- The lift to the represented pullback lies over the original geometric point. -/
private theorem closedImmersionPullbackNeighborhood_fac (zbar : GeometricPoint Z)
    (N : SmallEtaleNeighborhood (zbar.map i)) :
    ofOverMap (closedImmersionPullbackLift i zbar N) ≫
        (closedImmersionPullbackChart i N.toSite).hom = zbar.hom := sorry

set_option backward.privateInPublic true in
private def closedImmersionPullbackNeighborhood (zbar : GeometricPoint Z)
    (N : SmallEtaleNeighborhood (zbar.map i)) : SmallEtaleNeighborhood zbar :=
  SmallEtaleNeighborhood.of (closedImmersionPullbackChart i N.toSite)
    (closedImmersionPullbackLift i zbar N)
    (closedImmersionPullbackNeighborhood_fac i zbar N)

set_option backward.privateInPublic true in
private def closedImmersionPullbackArrow (U : smallEtaleSite X) :
    (smallEtaleToSpaces Z).obj (closedImmersionPullbackChart i U) ⟶
      (etaleBaseChange i).obj U :=
  MorphismProperty.Over.homMk
    (pullback.lift ((closedImmersionRepresentable i).fst U.hom)
      (yoneda.map ((closedImmersionRepresentable i).snd U.hom))
      ((closedImmersionRepresentable i).w U.hom))
    (by
      change pullback.lift _ _ _ ≫ pullback.fst (homFunctor i) (homFunctor U.hom) = _
      exact pullback.lift_fst _ _ _)

set_option backward.privateInPublic true in
private def closedImmersionSectionComponent
    (F : Sheaf (smallEtaleTopology Z) (Type (u + 1))) (U : smallEtaleSite X) :
    ((sheafPushforward (Type (u + 1)) i).obj F).obj.obj (op U) →
      F.obj.obj (op (closedImmersionPullbackChart i U)) :=
  fun σ ↦
    (limit.π
      (StructuredArrow.proj (op ((etaleBaseChange i).obj U)) (smallEtaleToSpaces Z).op ⋙ F.obj)
      (StructuredArrow.mk (closedImmersionPullbackArrow i U).op))
      (((smallEtaleToSpaces Z).op.ranObjObjIsoLimit F.obj
        (op ((etaleBaseChange i).obj U))).hom σ)

set_option backward.privateInPublic true in
private def closedImmersionStalkComponent
    (F : Sheaf (smallEtaleTopology Z) (Type (u + 1))) (zbar : GeometricPoint Z)
    (N : SmallEtaleNeighborhood (zbar.map i))
    (σ : ((sheafPushforward (Type (u + 1)) i).obj F).obj.obj (op N.toSite)) :
    stalk zbar F.obj :=
  toStalk (closedImmersionPullbackNeighborhood i zbar N)
    (closedImmersionSectionComponent i F N.toSite σ)

set_option backward.privateInPublic true in
/-- Evaluation on represented pullbacks is compatible with restriction of germs. -/
private theorem closedImmersionStalkComponent_naturality
    (F : Sheaf (smallEtaleTopology Z) (Type (u + 1))) (zbar : GeometricPoint Z)
    {N N' : SmallEtaleNeighborhood (zbar.map i)} (f : N ⟶ N')
    (σ : ((sheafPushforward (Type (u + 1)) i).obj F).obj.obj (op N'.toSite)) :
    closedImmersionStalkComponent i F zbar N
        (((sheafPushforward (Type (u + 1)) i).obj F).obj.map f.val.op σ) =
      closedImmersionStalkComponent i F zbar N' σ := sorry

-- Module visibility justification: retain the pullback and evaluation constructions as private
-- implementation details of the public comparison, as in the existing field-valued-point API.
set_option backward.privateInPublic true in
/-- The canonical comparison from the direct-image stalk at the image of a geometric point
to the original stalk, obtained by evaluating sections on pulled-back étale neighborhoods. -/
def stalkPushforwardClosedImmersion
    (F : Sheaf (smallEtaleTopology Z) (Type (u + 1))) (zbar : GeometricPoint Z) :
    stalk (zbar.map i) ((sheafPushforward (Type (u + 1)) i).obj F).obj →
      stalk zbar F.obj :=
  by
    exact (sectionsDiagram (zbar.map i)
      ((sheafPushforward (Type (u + 1)) i).obj F).obj).descColimitType
      { pt := stalk zbar F.obj
        ι := fun N σ ↦ closedImmersionStalkComponent i F zbar N.unop σ
        ι_naturality := fun f ↦ funext fun σ ↦
          closedImmersionStalkComponent_naturality i F zbar f.unop σ }

-- Module visibility justification: state the germ computation using the same private
-- pullback and evaluation constructions without adding public implementation names.
set_option backward.privateInPublic true in
/-- The canonical stalk comparison sends a germ to the germ of its evaluation on the
represented pullback of its étale neighborhood. -/
theorem stalkPushforwardClosedImmersion_toStalk
    (F : Sheaf (smallEtaleTopology Z) (Type (u + 1))) (zbar : GeometricPoint Z)
    (N : SmallEtaleNeighborhood (zbar.map i))
    (σ : ((sheafPushforward (Type (u + 1)) i).obj F).obj.obj (op N.toSite)) :
    stalkPushforwardClosedImmersion i F zbar (toStalk N σ) =
      toStalk (closedImmersionPullbackNeighborhood i zbar N)
        (closedImmersionSectionComponent i F N.toSite σ) := sorry

end GeometricPoint

/-- For a closed immersion of algebraic spaces, the canonical map from the direct-image
stalk at the image of a geometric point to the original stalk is bijective. -/
theorem stalk_pushforward_closedImmersion
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf (smallEtaleTopology Z) (Type (u + 1))) (zbar : GeometricPoint Z) :
    Function.Bijective (GeometricPoint.stalkPushforwardClosedImmersion i F zbar) := sorry

end AlgebraicGeometry.AlgebraicSpace
