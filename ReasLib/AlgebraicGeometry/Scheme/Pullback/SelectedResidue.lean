/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Residue data at a selected point of a scheme pullback

A compatible map of residue fields gives a morphism from `Spec κ(x)` to the
pullback. The selected point is its value at the unique point of this spectrum.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.SelectedResidue

/-- The native residue equivalence for the unique point of a field spectrum. -/
def fieldSpecResidueEquiv (K : Type u) [Field K] :
    (Spec (CommRingCat.of K)).residueField default ≃+* K :=
  (Scheme.Spec.residueFieldIso (CommRingCat.of K) default).commRingCatIsoToRingEquiv.trans
    (Ideal.algEquivResidueFieldOfField
      ((default : Spec (CommRingCat.of K)).asIdeal)).toRingEquiv.symm

/-- The canonical residue-point morphism induces the inverse of the native
field-Spec residue equivalence, after its point transport. -/
theorem fromSpecResidueField_forward_apply {X : Scheme.{u}} (x : X)
    (a : X.residueField x) :
    fieldSpecResidueEquiv (X.residueField x)
      ((X.fromSpecResidueField x).residueFieldMap default
        ((X.residueFieldCongr (X.fromSpecResidueField_apply x default)).inv a)) = a := by
  -- Concrete equality debt: the canonical morphism `Spec κ(x) ⟶ X`
  -- corresponds to `(x, id)` under native `Scheme.SpecToEquivOfField`.
  -- `Spec.residueFieldIso` and `Ideal.algEquivResidueFieldOfField` identify
  -- its induced residue map with that identity, including point transport.
  sorry

/-- Residue-map composition with explicit transport to a common endpoint. -/
theorem residueFieldMap_of_comp_eq {A B C : Scheme.{u}}
    (r : A ⟶ B) (q : B ⟶ C) (t : A ⟶ C) (e : r ≫ q = t)
    (a : A) (c : C) (hr : q (r a) = c) (ht : t a = c) :
    (C.residueFieldCongr hr).inv ≫ q.residueFieldMap (r a) ≫ r.residueFieldMap a =
      (C.residueFieldCongr ht).inv ≫ t.residueFieldMap a := by
  subst t
  rw [Scheme.residueFieldMap_comp]
  simp

variable {X S U : Scheme.{u}} (f : X ⟶ S) (g : U ⟶ S)
  (x : X) (n : U) (η : U.residueField n →+* X.residueField x)
  (h : (AlgebraicGeometry.Spec.map (CommRingCat.ofHom η) ≫
      U.fromSpecResidueField n) ≫ g = X.fromSpecResidueField x ≫ f)

/-- The pointed morphism supplied by the given residue homomorphism. -/
def lift : Spec (X.residueField x) ⟶ pullback f g :=
  pullback.lift (X.fromSpecResidueField x)
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom η) ≫ U.fromSpecResidueField n)
    h.symm

/-- The selected lift has the prescribed first component. -/
@[simp]
theorem lift_fst : lift f g x n η h ≫ pullback.fst f g = X.fromSpecResidueField x :=
  pullback.lift_fst _ _ _

/-- The selected lift has the prescribed second component. -/
@[simp]
theorem lift_snd : lift f g x n η h ≫ pullback.snd f g =
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom η) ≫ U.fromSpecResidueField n :=
  pullback.lift_snd _ _ _

/-- The actual point obtained by evaluating the pointed lift. -/
def point : (pullback f g : Scheme) :=
  lift f g x n η h default

/-- The first projection of the selected point is the input point of `X`. -/
@[simp]
theorem point_fst : pullback.fst f g (point f g x n η h) = x := by
  calc
    pullback.fst f g (point f g x n η h) =
        (lift f g x n η h ≫ pullback.fst f g) default :=
      (Scheme.Hom.comp_apply _ _ _).symm
    _ = X.fromSpecResidueField x default :=
      congrArg (fun k : Spec (X.residueField x) ⟶ X ↦ k default) (lift_fst f g x n η h)
    _ = x := X.fromSpecResidueField_apply x default

/-- The second projection of the selected point is the input point of `U`. -/
@[simp]
theorem point_snd : pullback.snd f g (point f g x n η h) = n := by
  calc
    pullback.snd f g (point f g x n η h) =
        (lift f g x n η h ≫ pullback.snd f g) default :=
      (Scheme.Hom.comp_apply _ _ _).symm
    _ = (AlgebraicGeometry.Spec.map (CommRingCat.ofHom η) ≫
        U.fromSpecResidueField n) default :=
      congrArg (fun k : Spec (X.residueField x) ⟶ U ↦ k default) (lift_snd f g x n η h)
    _ = U.fromSpecResidueField n
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom η) default) :=
      Scheme.Hom.comp_apply _ _ _
    _ = n := U.fromSpecResidueField_apply n _

/-- The forward residue map comes from the actual lift and the native field-Spec
residue equivalence. -/
def residueForward : (pullback f g).residueField (point f g x n η h) →+*
    X.residueField x :=
  (fieldSpecResidueEquiv (X.residueField x)).toRingHom.comp
    ((lift f g x n η h).residueFieldMap default).hom

/-- The inverse residue map comes from the first projection, after transporting
along its proved point equation. -/
def residueInverse : X.residueField x →+*
    (pullback f g).residueField (point f g x n η h) :=
  ((X.residueFieldCongr (point_fst f g x n η h)).inv ≫
    (pullback.fst f g).residueFieldMap (point f g x n η h)).hom

/-- Residue-map naturality for `lift ≫ fst = fromSpecResidueField` identifies
the forward map after the explicit inverse with the identity. -/
theorem forward_comp_inverse :
    (residueForward f g x n η h).comp (residueInverse f g x n η h) =
      RingHom.id (X.residueField x) := by
  ext a
  have hn := residueFieldMap_of_comp_eq (lift f g x n η h) (pullback.fst f g)
    (X.fromSpecResidueField x) (lift_fst f g x n η h) default x
    (point_fst f g x n η h) (X.fromSpecResidueField_apply x default)
  exact (congrArg (fun k : X.residueField x ⟶
      (Spec (X.residueField x)).residueField default ↦
        fieldSpecResidueEquiv (X.residueField x) (k a)) hn).trans
    (fromSpecResidueField_forward_apply x a)

/-- The other inverse law follows from injectivity of the forward field hom. -/
theorem inverse_comp_forward :
    (residueInverse f g x n η h).comp (residueForward f g x n η h) =
      RingHom.id ((pullback f g).residueField (point f g x n η h)) := by
  ext a
  apply (residueForward f g x n η h).injective
  exact DFunLike.congr_fun (forward_comp_inverse f g x n η h)
    (residueForward f g x n η h a)

/-- The residue equivalence at the selected pullback point, packaged from its
two explicit ring homomorphisms. -/
def residueEquiv : (pullback f g).residueField (point f g x n η h) ≃+*
    X.residueField x :=
  RingEquiv.ofRingHom (residueForward f g x n η h) (residueInverse f g x n η h)
    (forward_comp_inverse f g x n η h) (inverse_comp_forward f g x n η h)

/-- The forward function of `residueEquiv` is the induced residue map of the lift. -/
@[simp]
theorem residueEquiv_toRingHom : (residueEquiv f g x n η h).toRingHom =
    residueForward f g x n η h := rfl

/-- The inverse function of `residueEquiv` is the induced residue map of `fst`. -/
@[simp]
theorem residueEquiv_symm_toRingHom : (residueEquiv f g x n η h).symm.toRingHom =
    residueInverse f g x n η h := rfl

/-- The canonical residue map from `κ(n)` comes from the second projection,
with transport along its proved point equation. -/
def canonicalMap : U.residueField n →+*
    (pullback f g).residueField (point f g x n η h) :=
  ((U.residueFieldCongr (point_snd f g x n η h)).inv ≫
    (pullback.snd f g).residueFieldMap (point f g x n η h)).hom

/-- The selected residue equivalence carries the canonical second-projection
residue map to the given homomorphism `η`. -/
theorem canonical_map_commutes :
    (residueEquiv f g x n η h).toRingHom.comp (canonicalMap f g x n η h) = η := by
  -- Concrete equality debt: apply residue-map naturality to `lift_snd`.
  -- The induced map of `Spec.map η` is `η` after the two native field-Spec
  -- residue equivalences; the point congruences are exactly `point_snd`.
  sorry

end AlgebraicGeometry.Scheme.SelectedResidue
