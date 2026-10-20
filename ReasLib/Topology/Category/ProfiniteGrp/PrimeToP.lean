/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import ReasLib.Topology.Algebra.OpenNormalSubgroup

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ProfiniteGrp

/-- Open normal subgroups whose finite quotients have order coprime to `p`. -/
def primeToPOpenNormal (G : ProfiniteGrp.{u}) (p : ℕ) :
    ObjectProperty (OpenNormalSubgroup G) :=
  fun N => p.Coprime (Nat.card (G ⧸ N.toSubgroup))

/-- The diagram of finite prime-to-`p` quotients of a profinite group, viewed in `ProfiniteGrp`. -/
def primeToPQuotientDiagram (G : ProfiniteGrp.{u}) (p : ℕ) :
    (primeToPOpenNormal G p).FullSubcategory ⥤ ProfiniteGrp.{u} :=
  (primeToPOpenNormal G p).ι ⋙ diagram G

/-- Objects of the prime-to-`p` quotient diagram are the corresponding finite quotients of `G`. -/
theorem primeToPQuotientDiagram_obj (G : ProfiniteGrp.{u}) (p : ℕ)
    (N : (primeToPOpenNormal G p).FullSubcategory) :
    (primeToPQuotientDiagram G p).obj N = (diagram G).obj N.obj := sorry

/-- Membership in the prime-to-`p` open-normal predicate is coprimeness of the quotient order. -/
theorem mem_primeToPOpenNormal (G : ProfiniteGrp.{u}) (p : ℕ) (N : OpenNormalSubgroup G) :
    primeToPOpenNormal G p N ↔ p.Coprime (Nat.card (G ⧸ N.toSubgroup)) := sorry

/-- The restricted prime-to-`p` finite-quotient diagram has a limit in `ProfiniteGrp`. -/
instance hasLimit_primeToPQuotientDiagram (G : ProfiniteGrp.{u}) (p : ℕ) :
    HasLimit (primeToPQuotientDiagram G p) := inferInstance

/-- The maximal prime-to-`p` quotient of a profinite group. -/
abbrev primeToPQuotient (G : ProfiniteGrp.{u}) (p : ℕ) : ProfiniteGrp.{u} :=
  CategoryTheory.Limits.limit (primeToPQuotientDiagram G p)

/-- The canonical projection from the maximal prime-to-`p` quotient onto a coprime finite quotient. -/
def primeToPQuotient.π (G : ProfiniteGrp.{u}) (p : ℕ)
    (N : (primeToPOpenNormal G p).FullSubcategory) :
    primeToPQuotient G p ⟶ (primeToPQuotientDiagram G p).obj N :=
  CategoryTheory.Limits.limit.π (primeToPQuotientDiagram G p) N

/-- Pullback of a prime-to-`p` open normal subgroup along a morphism of profinite groups. -/
def primeToPOpenNormal.preimage {G H : ProfiniteGrp.{u}} (p : ℕ) (φ : G ⟶ H)
    (N : (primeToPOpenNormal H p).FullSubcategory) :
    (primeToPOpenNormal G p).FullSubcategory :=
  ⟨N.obj.comap φ.hom φ.hom.continuous, sorry⟩

/-- The finite quotient map induced by a morphism of profinite groups on a comap of an open
normal subgroup. -/
def quotientMapOfComap {G H : ProfiniteGrp.{u}} (φ : G ⟶ H) (N : OpenNormalSubgroup H) :
    (diagram G).obj (N.comap φ.hom φ.hom.continuous) ⟶ (diagram H).obj N :=
  (forget₂ FiniteGrp ProfiniteGrp).map (FiniteGrp.ofHom (MonoidHom.mk'
    (Quotient.lift (fun g : G => (QuotientGroup.mk (φ.hom g) : H ⧸ N.toSubgroup)) sorry)
    sorry))

/-- A continuous homomorphism of profinite groups induces a morphism of maximal prime-to-`p`
quotients. -/
def primeToPQuotientMap {G H : ProfiniteGrp.{u}} (p : ℕ) (φ : G ⟶ H) :
    primeToPQuotient G p ⟶ primeToPQuotient H p :=
  CategoryTheory.Limits.limit.lift (primeToPQuotientDiagram H p)
    { pt := primeToPQuotient G p
      π :=
        { app := fun N =>
            (primeToPQuotient.π G p (primeToPOpenNormal.preimage p φ N) ≫
              quotientMapOfComap φ N.obj :
              primeToPQuotient G p ⟶ (primeToPQuotientDiagram H p).obj N)
          naturality := fun _ _ _ => sorry } }

/-- The induced prime-to-`p` quotient map of the identity is the identity. -/
theorem primeToPQuotientMap_id (G : ProfiniteGrp.{u}) (p : ℕ) :
    primeToPQuotientMap p (𝟙 G) = 𝟙 (primeToPQuotient G p) := sorry

/-- The induced prime-to-`p` quotient map preserves composition. -/
theorem primeToPQuotientMap_comp {G H K : ProfiniteGrp.{u}} (p : ℕ) (φ : G ⟶ H) (ψ : H ⟶ K) :
    primeToPQuotientMap p (φ ≫ ψ) =
      primeToPQuotientMap p φ ≫ primeToPQuotientMap p ψ := sorry

/-- Applying `primeToPQuotientMap` at a coprime finite quotient recovers the induced finite
quotient map. -/
theorem primeToPQuotientMap_π {G H : ProfiniteGrp.{u}} (p : ℕ) (φ : G ⟶ H)
    (N : (primeToPOpenNormal H p).FullSubcategory) :
    primeToPQuotientMap p φ ≫ primeToPQuotient.π H p N =
      primeToPQuotient.π G p (primeToPOpenNormal.preimage p φ N) ≫
        quotientMapOfComap φ N.obj := sorry

end ProfiniteGrp
