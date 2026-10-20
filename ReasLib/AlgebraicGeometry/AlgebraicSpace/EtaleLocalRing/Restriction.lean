/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing

/-!
# Étale local rings and restriction

The identity on sections induces mutually inverse local-ring maps along an étale morphism.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {U X : AlgebraicSpace S}

/-- Identity-on-sections comparison of structure sheaves after postcomposition of étale
objects. -/
def restrictStructurePresheafIso (j : U ⟶ X) [Etale j] :
    (structureSheaf U).obj ≅ (etaleRestriction j).op ⋙ (structureSheaf X).obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- Identity-on-sections map of étale local rings `𝒪_{U, ubar} →+* 𝒪_{X, ubar.map j}`,
sending the germ of a section over `V` to the germ of the same section over the
postcomposed neighbourhood of `ubar.map j`. -/
def etaleLocalRingHom (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U) :
    etaleLocalRing U ubar →+* etaleLocalRing X (ubar.map j) :=
  RingCat.Hom.hom <|
    (toSmallEtalePoint ubar).presheafFiberDesc
      (fun V l ↦
        (restrictStructurePresheafIso j).hom.app (op V) ≫
          (toSmallEtalePoint (ubar.map j)).toPresheafFiber ((etaleRestriction j).obj V)
            (restrictPostcomposeLift j ubar l) (structureSheaf X).obj)
      (fun _ _ _ _ ↦ sorry)

/-- Opposite map of étale local rings `𝒪_{X, ubar.map j} →+* 𝒪_{U, ubar}`, obtained by
descending along the scheme projection of the represented atlas refinement. -/
def etaleLocalRingInvHom (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U) :
    etaleLocalRing X (ubar.map j) →+* etaleLocalRing U ubar :=
  RingCat.Hom.hom <|
    (toSmallEtalePoint (ubar.map j)).presheafFiberDesc
      (fun W l ↦
        (structureSheaf X).obj.map (op (restrictRefinementHom j W)) ≫
          (restrictStructurePresheafIso j).inv.app
              (op (restrictRefinementObj j W)) ≫
            (toSmallEtalePoint ubar).toPresheafFiber
              (restrictRefinementObj j W)
              (restrictRefinementLift j ubar l) (structureSheaf U).obj)
      (fun _ _ _ _ ↦ sorry)

/-- The identity-on-sections local ring map is inverse to `etaleLocalRingInvHom`. -/
theorem etaleLocalRingHom_comp_inv (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U) :
    (etaleLocalRingInvHom j ubar).comp (etaleLocalRingHom j ubar) =
      RingHom.id (etaleLocalRing U ubar) :=
  sorry

/-- The fibre-product local ring map is inverse to `etaleLocalRingHom`. -/
theorem etaleLocalRingInvHom_comp (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U) :
    (etaleLocalRingHom j ubar).comp (etaleLocalRingInvHom j ubar) =
      RingHom.id (etaleLocalRing X (ubar.map j)) :=
  sorry

/-- For an étale morphism, the identity-on-sections map of étale local rings is an
isomorphism. -/
instance etaleLocalRingHom_isIso (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U) :
    IsIso (RingCat.ofHom (etaleLocalRingHom j ubar)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
