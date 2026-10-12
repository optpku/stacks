/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.RingTheory.Ideal.Cotangent.Equiv

/-!
# Change of presentation for conormal sheaves

An isomorphism between two presenting ring sheaves which commutes with their maps to a
common quotient ring sheaf induces an explicit isomorphism between the corresponding conormal
sheaves.  Both directions are constructed from the sectionwise maps on ideal cotangent modules.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite.InverseImage

noncomputable section

universe u

namespace SheafOfModules.RingedSite.Conormal.ChangeOfPresentation

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {P P' B : Sheaf J CommRingCat.{u}}

/-- The canonical map from a sheaf to its pushforward along the identity functor. -/
noncomputable def toIdentityPushforward (Q : Sheaf J CommRingCat.{u}) :
    Q ⟶ ((Functor.id C).sheafPushforwardContinuous CommRingCat.{u} J J).obj Q :=
  (Functor.sheafPushforwardContinuousId CommRingCat.{u} J).inv.app Q

/-- The maps to identity pushforward commute with every morphism of ring sheaves. -/
theorem toIdentityPushforward_naturality {Q Q' : Sheaf J CommRingCat.{u}}
    (f : Q ⟶ Q') :
    toIdentityPushforward Q ≫
        ((Functor.id C).sheafPushforwardContinuous CommRingCat.{u} J J).map f =
      f ≫ toIdentityPushforward Q' := by
  simpa only [toIdentityPushforward, Functor.id_obj, Functor.id_map] using
    (Functor.sheafPushforwardContinuousId CommRingCat.{u} J).inv.naturality f |>.symm

/-- The identity-site presentation of the identity morphism of a commutative ring sheaf. -/
noncomputable abbrev identityMap (B : Sheaf J CommRingCat.{u}) :
    B ⟶ ((Functor.id C).sheafPushforwardContinuous CommRingCat.{u} J J).obj B :=
  toIdentityPushforward B

/-- An isomorphism of presenting ring sheaves and a commuting triangle give the adjoint-side
square used by the explicit conormal comparison. -/
theorem square (alpha : P ⟶ B) (alpha' : P' ⟶ B) (e : P ≅ P')
    (h : e.hom ≫ alpha' = alpha) :
    CommSq
      (e.hom ≫ toIdentityPushforward P') alpha
      (((Functor.id C).sheafPushforwardContinuous CommRingCat.{u} J J).map alpha')
      (identityMap B) := by
  refine ⟨?_⟩
  simp only [Category.assoc, toIdentityPushforward_naturality]
  rw [← Category.assoc, h]

/-- The explicit conormal comparison in the direction of an isomorphism of presentations. -/
noncomputable def comparisonHom (alpha : P ⟶ B) (alpha' : P' ⟶ B)
    (e : P ≅ P') (h : e.hom ≫ alpha' = alpha) :
    conormalSource alpha ⟶ conormalSource alpha' :=
  (SheafOfModules.RingedSite.extendIdIso B).inv.app (conormalSource alpha) ≫
    (SheafOfModules.RingedSite.pullbackExtendIso (𝟙 B)).inv.app
      (conormalSource alpha) ≫
    SheafOfModules.RingedSite.Conormal.InverseImage.comparison
      (J := J) (K := J) (Functor.id C)
      (e.hom ≫ toIdentityPushforward P')
      (identityMap B) (square alpha alpha' e h)

/-- The reverse conormal comparison is obtained by applying the same sectionwise construction
to the inverse presentation isomorphism. -/
noncomputable def comparisonInv (alpha : P ⟶ B) (alpha' : P' ⟶ B)
    (e : P ≅ P') (h : e.hom ≫ alpha' = alpha) :
    conormalSource alpha' ⟶ conormalSource alpha :=
  comparisonHom alpha' alpha e.symm (by
    change e.inv ≫ alpha = alpha'
    rw [← h]
    exact e.inv_hom_id_assoc alpha')

/-- The forward and reverse sectionwise change-of-presentation maps compose to the identity. -/
theorem comparison_hom_inv_id (alpha : P ⟶ B) (alpha' : P' ⟶ B)
    (e : P ≅ P') (h : e.hom ≫ alpha' = alpha) :
    comparisonHom alpha alpha' e h ≫ comparisonInv alpha alpha' e h = 𝟙 _ := sorry

/-- The reverse and forward sectionwise change-of-presentation maps compose to the identity. -/
theorem comparison_inv_hom_id (alpha : P ⟶ B) (alpha' : P' ⟶ B)
    (e : P ≅ P') (h : e.hom ≫ alpha' = alpha) :
    comparisonInv alpha alpha' e h ≫ comparisonHom alpha alpha' e h = 𝟙 _ := sorry

/-- Isomorphic presentations of the same quotient ring sheaf have canonically isomorphic
conormal sheaves. -/
noncomputable def comparisonIso (alpha : P ⟶ B) (alpha' : P' ⟶ B)
    (e : P ≅ P') (h : e.hom ≫ alpha' = alpha) :
    conormalSource alpha ≅ conormalSource alpha' where
  hom := comparisonHom alpha alpha' e h
  inv := comparisonInv alpha alpha' e h
  hom_inv_id := comparison_hom_inv_id alpha alpha' e h
  inv_hom_id := comparison_inv_hom_id alpha alpha' e h

end SheafOfModules.RingedSite.Conormal.ChangeOfPresentation
