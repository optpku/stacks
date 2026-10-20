/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Map
public import Mathlib.CategoryTheory.Sites.Point.Category

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

@[expose] public section

set_option backward.privateInPublic true

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- A scheme over a base with a geometric closed point and uniquely normalized
lifts of pointed étale neighborhoods. -/
structure StrictHenselianNeighborhood {S X : Scheme.{u}} (s : GeometricPoint S)
    (p : X ⟶ S) where
  /-- The specified geometric closed point. -/
  closedPoint : Spec (.of s.K) ⟶ X
  /-- The geometric closed point projects to the given point of the base. -/
  closedPoint_over : closedPoint ≫ p = s.hom
  /-- The normalized lift to a pointed étale neighborhood. -/
  lift (U : S.Etale) (point : s.toSmallEtalePoint.fiber.obj U) :
    Over.mk p ⟶ (Etale.forget S).obj U
  /-- The normalized lift preserves the specified geometric point. -/
  lift_closedPoint (U : S.Etale) (point : s.toSmallEtalePoint.fiber.obj U) :
    closedPoint ≫ (lift U point).left = point.left
  /-- Any over-base lift preserving the geometric point is the normalized lift. -/
  lift_unique (U : S.Etale) (point : s.toSmallEtalePoint.fiber.obj U)
      (other : Over.mk p ⟶ (Etale.forget S).obj U)
      (hother : closedPoint ≫ other.left = point.left) : other = lift U point

/-- Construct a pointed scheme with uniquely normalized étale lifts from explicit data. -/
def StrictHenselianNeighborhood.ofLifts {S X : Scheme.{u}} {s : GeometricPoint S}
    {p : X ⟶ S} (closedPoint : Spec (.of s.K) ⟶ X)
    (closedPoint_over : closedPoint ≫ p = s.hom)
    (lift : (U : S.Etale) → s.toSmallEtalePoint.fiber.obj U →
      (Over.mk p ⟶ (Etale.forget S).obj U))
    (lift_closedPoint : ∀ U point, closedPoint ≫ (lift U point).left = point.left)
    (lift_unique : ∀ U point (other : Over.mk p ⟶ (Etale.forget S).obj U),
      closedPoint ≫ other.left = point.left → other = lift U point) :
    StrictHenselianNeighborhood s p :=
  ⟨closedPoint, closedPoint_over, lift, lift_closedPoint, lift_unique⟩

namespace StrictHenselization

variable {S : Scheme.{u}} (s : GeometricPoint S)

/-- Evaluation of functions on a pointed étale neighborhood in the geometric residue field. -/
private def residueEvaluation (U : S.Etale)
    (point : s.toSmallEtalePoint.fiber.obj U) :
    ((S.smallEtaleToScheme.op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat).obj (op U)) ⟶
      RingCat.of s.K :=
  (forget₂ CommRingCat RingCat).map
    (Scheme.Γ.map point.left.op ≫ (Scheme.ΓSpecIso (.of s.K)).hom)

/-- Residue evaluation commutes with morphisms of pointed étale neighborhoods. -/
theorem closedPoint_naturality {U V : S.Etale} (morphism : U ⟶ V)
    (point : s.toSmallEtalePoint.fiber.obj U) :
    (S.smallEtaleToScheme.op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map morphism.op ≫
        residueEvaluation s U point =
      residueEvaluation s V (s.toSmallEtalePoint.fiber.map morphism point) := sorry

/-- The geometric closed point of a strict henselization, obtained by residue evaluation. -/
def closedPoint : Spec (.of s.K) ⟶ strictHenselizationAt S s :=
  Spec.map (CommRingCat.ofHom (RingCat.Hom.hom
    (s.toSmallEtalePoint.presheafFiberDesc (residueEvaluation s)
      (fun _ _ morphism point ↦ closedPoint_naturality s morphism point))))

/-- The closed geometric point of a strict henselization lies over its geometric point. -/
theorem closedPoint_over : closedPoint s ≫ toScheme S s = s.hom := sorry

variable (U : S.Etale) (point : s.toSmallEtalePoint.fiber.obj U)

/-- An open neighborhood of the lifted geometric point contains its entire spectrum. -/
theorem lift_open_range (V : OpenNhds (point.left (default : Spec (.of s.K)))) :
    Set.range point.left ⊆ Set.range (Scheme.Opens.ι V.1) := sorry

/-- The geometric lift to an open neighborhood is a point over the original base. -/
theorem lift_open_over (V : OpenNhds (point.left (default : Spec (.of s.K)))) :
    IsOpenImmersion.lift (Scheme.Opens.ι V.1) point.left (lift_open_range s U point V) ≫
        (Scheme.Opens.ι V.1 ≫ U.hom) = s.hom := sorry

/-- An open-neighborhood function determines a germ in the étale local ring at the base point. -/
private def liftOpenGerm
    (V : OpenNhds (point.left (default : Spec (.of s.K)))) :
    U.left.presheaf.obj (op V.1) ⟶ etaleLocalRing.asCommRing S s :=
  let openSubset : U.left.Opens := V.1
  let neighborhood : S.Etale :=
    MorphismProperty.Over.mk _ (Scheme.Opens.ι openSubset ≫ U.hom)
      (MorphismProperty.comp_mem @Etale (Scheme.Opens.ι openSubset) U.hom
        inferInstance U.prop)
  let liftedPoint : Spec (.of s.K) ⟶ openSubset.toScheme :=
    IsOpenImmersion.lift (Scheme.Opens.ι openSubset)
      (point.left : Spec (.of s.K) ⟶ U.left) (lift_open_range s U point V)
  let fiberPoint : s.toSmallEtalePoint.fiber.obj neighborhood :=
    Over.homMk liftedPoint (lift_open_over s U point V)
  CommRingCat.Hom.hom openSubset.topIso.inv |>
    fun restriction ↦ CommRingCat.ofHom
      ((RingCat.Hom.hom (s.toSmallEtalePoint.toPresheafFiber neighborhood fiberPoint
        (S.smallEtaleToScheme.op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat))).comp restriction)

/-- The open-neighborhood germs used to lift an étale neighborhood are compatible
with restriction. -/
theorem lift_germ_compatible
    {V W : (OpenNhds (X := (U.left : TopCat))
      (point.left (default : Spec (.of s.K))))ᵒᵖ}
    (morphism : V ⟶ W) :
    ((OpenNhds.inclusion (point.left (default : Spec (.of s.K)))).op ⋙
        U.left.presheaf).map morphism ≫
        liftOpenGerm s U point W.unop = liftOpenGerm s U point V.unop := sorry

/-- The map from a neighborhood's Zariski stalk to the base étale local ring. -/
private def liftStalkMap :
    U.left.presheaf.stalk (point.left (default : Spec (.of s.K))) ⟶
    etaleLocalRing.asCommRing S s :=
  colimit.desc ((OpenNhds.inclusion (point.left (default : Spec (.of s.K)))).op ⋙
      U.left.presheaf)
    { pt := etaleLocalRing.asCommRing S s
      ι := { app := fun V ↦ liftOpenGerm s U point V.unop
             naturality := fun _ _ morphism ↦ lift_germ_compatible s U point morphism } }

/-- The normalized lift from a strict henselization to a pointed étale neighborhood. -/
def lift : strictHenselizationAt S s ⟶ U.left :=
  Spec.map (liftStalkMap s U point) ≫
    U.left.fromSpecStalk (point.left (default : Spec (.of s.K)))

/-- The normalized étale lift is a morphism over the base scheme. -/
theorem lift_over : lift s U point ≫ U.hom = toScheme S s := sorry

/-- The normalized étale lift sends the closed geometric point to the prescribed lift. -/
theorem lift_closedPoint : closedPoint s ≫ lift s U point = point.left := sorry

/-- An étale lift preserving the closed geometric point is uniquely normalized. -/
theorem lift_unique (other : Over.mk (toScheme S s) ⟶ (Etale.forget S).obj U)
    (hother : closedPoint s ≫ other.left = point.left) :
    other = Over.homMk (lift s U point) (lift_over s U point) := sorry

end StrictHenselization

/-- The canonical pointed strict henselization, with lifts constructed from Zariski germs. -/
def StrictHenselianNeighborhood.canonical {S : Scheme.{u}} (s : GeometricPoint S) :
    StrictHenselianNeighborhood s (StrictHenselization.toScheme S s) :=
  StrictHenselianNeighborhood.ofLifts (StrictHenselization.closedPoint s)
    (StrictHenselization.closedPoint_over s)
    (fun U point ↦ Over.homMk (StrictHenselization.lift s U point)
      (StrictHenselization.lift_over s U point))
    (StrictHenselization.lift_closedPoint s) (StrictHenselization.lift_unique s)

/-- The canonical lifts preserve the geometric point and are the unique over-base lifts
with that property. -/
theorem StrictHenselianNeighborhood.canonical_spec {S : Scheme.{u}} (s : GeometricPoint S)
    (U : S.Etale) (point : s.toSmallEtalePoint.fiber.obj U) :
    (canonical s).closedPoint ≫ ((canonical s).lift U point).left = point.left ∧
      ∀ (other : Over.mk (StrictHenselization.toScheme S s) ⟶ (Etale.forget S).obj U),
        (canonical s).closedPoint ≫ other.left = point.left →
          other = (canonical s).lift U point := sorry

/-- Retargeting a pointed étale neighborhood along a point of a normalized neighborhood
gives a geometric point over the base. -/
theorem StrictHenselianNeighborhood.specializationPoint_over {S X : Scheme.{u}}
    {s t : GeometricPoint S} {p : X ⟶ S} (neighborhood : StrictHenselianNeighborhood s p)
    (point : Spec (.of t.K) ⟶ X) (point_over : point ≫ p = t.hom)
    (U : S.Etale) (lift : s.toSmallEtalePoint.fiber.obj U) :
    (point ≫ (neighborhood.lift U lift).left) ≫ U.hom = t.hom := sorry

/-- Retargeting pointed étale neighborhoods commutes with étale morphisms. -/
theorem StrictHenselianNeighborhood.specializationPoint_naturality {S X : Scheme.{u}}
    {s t : GeometricPoint S} {p : X ⟶ S} (neighborhood : StrictHenselianNeighborhood s p)
    (point : Spec (.of t.K) ⟶ X) (point_over : point ≫ p = t.hom)
    {U V : S.Etale} (morphism : U ⟶ V) :
    s.toSmallEtalePoint.fiber.map morphism ≫
        (TypeCat.ofHom (fun lift ↦ Over.homMk (point ≫ (neighborhood.lift V lift).left)
          (neighborhood.specializationPoint_over point point_over V lift)) :
          s.toSmallEtalePoint.fiber.obj V ⟶ t.toSmallEtalePoint.fiber.obj V) =
      (TypeCat.ofHom (fun lift ↦ Over.homMk (point ≫ (neighborhood.lift U lift).left)
          (neighborhood.specializationPoint_over point point_over U lift)) :
          s.toSmallEtalePoint.fiber.obj U ⟶ t.toSmallEtalePoint.fiber.obj U) ≫
        t.toSmallEtalePoint.fiber.map morphism := sorry

/-- Geometric specialization retargets neighborhoods using their normalized lifts. -/
def StrictHenselianNeighborhood.specializationPoint {S X : Scheme.{u}}
    {s t : GeometricPoint S} {p : X ⟶ S} (neighborhood : StrictHenselianNeighborhood s p)
    (point : Spec (.of t.K) ⟶ X) (point_over : point ≫ p = t.hom) :
    t.toSmallEtalePoint ⟶ s.toSmallEtalePoint where
  hom := {
    app := fun U ↦ TypeCat.ofHom fun lift ↦
      Over.homMk (point ≫ (neighborhood.lift U lift).left)
        (neighborhood.specializationPoint_over point point_over U lift)
    naturality := fun _ _ morphism ↦
      neighborhood.specializationPoint_naturality point point_over morphism }

/-- The stalk specialization sends each neighborhood germ to its retargeted germ. -/
theorem StrictHenselianNeighborhood.specializationPoint_stalk {S X : Scheme.{u}}
    {s t : GeometricPoint S} {p : X ⟶ S} (neighborhood : StrictHenselianNeighborhood s p)
    (point : Spec (.of t.K) ⟶ X) (point_over : point ≫ p = t.hom)
    (F : Sheaf S.smallEtaleTopology (Type u)) (U : S.Etale)
    (lift : s.toSmallEtalePoint.fiber.obj U) :
    s.toSmallEtalePoint.toPresheafFiber U lift F.obj ≫
        ((neighborhood.specializationPoint point point_over).sheafFiber).app F =
      t.toSmallEtalePoint.toPresheafFiber U
        ((neighborhood.specializationPoint point point_over).hom.app U lift) F.obj := sorry

end AlgebraicGeometry.Scheme

end
