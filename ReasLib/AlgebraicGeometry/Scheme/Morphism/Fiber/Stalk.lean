/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Stalk

/-!
# Stalks at distinguished points of fibres

This leaf owns the local rings and canonical maps attached to the point of a
scheme-theoretic fibre determined by a point of the source.  It is independent
of tangent- and cotangent-space constructions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The local ring of the scheme-theoretic fibre `X_{f(x)}` at the point
`f.asFiber x` determined by `x`. -/
abbrev fiberStalkAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : CommRingCat :=
  (f.fiber (f x)).presheaf.stalk (f.asFiber x)

/-- The residue field of the distinguished fibre point `f.asFiber x`. -/
abbrev fiberResidueFieldAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : CommRingCat :=
  (f.fiber (f x)).residueField (f.asFiber x)

/-- The map from `κ(f(x))` to the stalk of the fibre at its distinguished
point, induced by the morphism from that fibre to `Spec κ(f(x))`. -/
noncomputable def fiberBaseResidueFieldToStalk
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    S.residueField (f x) ⟶ fiberStalkAt f x := by
  let e :
      (Spec (S.residueField (f x))).presheaf.stalk
          (IsLocalRing.closedPoint (S.residueField (f x))) ⟶
        (Spec (S.residueField (f x))).presheaf.stalk
          ((f.fiberToSpecResidueField (f x)) (f.asFiber x)) :=
    ((Spec (S.residueField (f x))).presheaf.stalkCongr
      (.of_eq (Scheme.Hom.fiberToSpecResidueField_apply f (f x) (f.asFiber x)).symm)).hom
  let phi1 :
      S.residueField (f x) ⟶
        (Spec (S.residueField (f x))).presheaf.stalk
          (IsLocalRing.closedPoint (S.residueField (f x))) :=
    (AlgebraicGeometry.stalkClosedPointIso (S.residueField (f x))).inv
  let phi2 :
      S.residueField (f x) ⟶
        (Spec (S.residueField (f x))).presheaf.stalk
          ((f.fiberToSpecResidueField (f x)) (f.asFiber x)) :=
    phi1 ≫ e
  exact phi2 ≫ (f.fiberToSpecResidueField (f x)).stalkMap (f.asFiber x)

/-- The point `f.asFiberHom x : Spec κ(x) ⟶ X_{f(x)}` induces a morphism
from the stalk of the fibre to the source residue field `κ(x)`. -/
noncomputable def fiberStalkToSourceResidueField
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    fiberStalkAt f x ⟶ X.residueField x := by
  let e :
      fiberStalkAt f x ⟶
        (f.fiber (f x)).presheaf.stalk
          ((f.asFiberHom x) (IsLocalRing.closedPoint (X.residueField x))) :=
    ((f.fiber (f x)).presheaf.stalkCongr (.of_eq (by simp))).inv
  exact e ≫ Scheme.stalkClosedPointTo (f.asFiberHom x)

/-- The fibre inclusion induces a morphism from the source stalk at `x` to
the stalk of the fibre at its distinguished point. -/
noncomputable def sourceStalkToFiberStalk
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    X.presheaf.stalk x ⟶ fiberStalkAt f x :=
  let e : X.presheaf.stalk x ⟶ X.presheaf.stalk ((f.fiberι (f x)) (f.asFiber x)) :=
    ((X.presheaf.stalkCongr (.of_eq (by simp))).inv)
  e ≫ (f.fiberι (f x)).stalkMap (f.asFiber x)

/-- The residue map of the base point and the fibre inclusion form the
canonical square on stalks at the distinguished point of the fibre. -/
theorem fiberBaseResidueFieldToStalk_fac
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    S.residue (f x) ≫ fiberBaseResidueFieldToStalk f x =
      f.stalkMap x ≫ sourceStalkToFiberStalk f x := sorry

/-- The base residue field `κ(f(x))` acts on the stalk of the fibre. -/
noncomputable instance fiberStalkBaseResidueFieldAlgebra
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Algebra (S.residueField (f x)) (fiberStalkAt f x) :=
  (fiberBaseResidueFieldToStalk f x).hom.toAlgebra

/-- The residue field of the distinguished fibre point is an algebra over its
local ring through the ordinary residue morphism. -/
noncomputable instance fiberStalkFiberResidueFieldAlgebra
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Algebra (fiberStalkAt f x) (fiberResidueFieldAt f x) :=
  ((f.fiber (f x)).residue (f.asFiber x)).hom.toAlgebra

/-- The `κ(f(x))`-action on the residue field of the distinguished fibre
point factors through its local ring. -/
instance fiberStalkFiberResidueFieldIsScalarTower
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsScalarTower (S.residueField (f x)) (fiberStalkAt f x) (fiberResidueFieldAt f x) := sorry

/-- The stalk of the fibre acts on the source residue field through the
distinguished fibre point. -/
noncomputable instance fiberStalkSourceResidueFieldAlgebra
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Algebra (fiberStalkAt f x) (X.residueField x) :=
  (fiberStalkToSourceResidueField f x).hom.toAlgebra

/-- The action of `κ(f(x))` on `κ(x)` factors through the stalk of the fibre
at its distinguished point. -/
instance fiberStalkSourceResidueFieldIsScalarTower
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsScalarTower (S.residueField (f x)) (fiberStalkAt f x) (X.residueField x) := sorry

/-- The source stalk acts on the stalk of the fibre through the fibre
inclusion. -/
noncomputable instance fiberStalkSourceStalkAlgebra
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Algebra (X.presheaf.stalk x) (fiberStalkAt f x) :=
  (sourceStalkToFiberStalk f x).hom.toAlgebra

/-- The canonical map from the distinguished fibre stalk to the source
residue field is a local ring homomorphism. -/
theorem fiberStalkToSourceResidueField_isLocalHom
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsLocalHom (fiberStalkToSourceResidueField f x).hom := sorry

/-- The local map from the distinguished fibre stalk to `κ(x)` induces a
map from the residue field of the fibre point to `κ(x)`. -/
noncomputable def fiberResidueFieldToSourceResidueField
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    fiberResidueFieldAt f x ⟶ X.residueField x :=
  CommRingCat.ofHom <|
    @IsLocalRing.ResidueField.lift
      (fiberStalkAt f x)
      (X.residueField x)
      inferInstance
      inferInstance
      inferInstance
      (fiberStalkToSourceResidueField f x).hom
      (fiberStalkToSourceResidueField_isLocalHom f x)

/-- The map from the distinguished fibre residue field to `κ(x)` is the
unique factorization of the fibre-stalk residue map. -/
theorem fiberStalkToSourceResidueField_factor
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    (f.fiber (f x)).residue (f.asFiber x) ≫
        fiberResidueFieldToSourceResidueField f x =
      fiberStalkToSourceResidueField f x := sorry

/-- The source residue field is an algebra over the distinguished fibre
residue field through the induced residue-field map. -/
noncomputable instance fiberResidueFieldSourceResidueFieldAlgebra
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Algebra (fiberResidueFieldAt f x) (X.residueField x) :=
  (fiberResidueFieldToSourceResidueField f x).hom.toAlgebra

/-- The action of the distinguished fibre stalk on `κ(x)` factors through
the residue field of the fibre point. -/
instance fiberResidueFieldSourceResidueFieldIsScalarTower
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsScalarTower (fiberStalkAt f x) (fiberResidueFieldAt f x)
      (X.residueField x) := sorry

/-- The induced map from the distinguished fibre residue field to `κ(x)` is
bijective. -/
theorem fiberResidueFieldToSourceResidueField_bijective
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Function.Bijective (fiberResidueFieldToSourceResidueField f x).hom := sorry

/-- The residue-field equivalence at the distinguished fibre point commutes
with the canonical maps from `κ(f(x))`. -/
theorem fiberResidueFieldAlgEquiv_commutes
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (r : S.residueField (f x)) :
    (RingEquiv.ofBijective (fiberResidueFieldToSourceResidueField f x).hom
      (fiberResidueFieldToSourceResidueField_bijective f x))
        ((algebraMap (S.residueField (f x)) (fiberResidueFieldAt f x)) r) =
      (algebraMap (S.residueField (f x)) (X.residueField x)) r := sorry

/-- The residue field of the distinguished fibre point is canonically
equivalent over `κ(f(x))` to the source residue field `κ(x)`. -/
noncomputable def fiberResidueFieldAlgEquiv
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    fiberResidueFieldAt f x ≃ₐ[S.residueField (f x)] X.residueField x :=
  let e : fiberResidueFieldAt f x ≃+* X.residueField x :=
    RingEquiv.ofBijective (fiberResidueFieldToSourceResidueField f x).hom
      (fiberResidueFieldToSourceResidueField_bijective f x)
  @AlgEquiv.ofRingEquiv (S.residueField (f x)) (fiberResidueFieldAt f x)
    (X.residueField x) _ _ _ _ _ e (fiberResidueFieldAlgEquiv_commutes f x)

/-- The induced map from the distinguished fibre residue field to `κ(x)`,
viewed as a linear map over the fibre stalk. -/
noncomputable def fiberResidueFieldToSourceResidueFieldLinearMap
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    fiberResidueFieldAt f x →ₗ[fiberStalkAt f x] X.residueField x :=
  (IsScalarTower.toAlgHom (fiberStalkAt f x) (fiberResidueFieldAt f x)
    (X.residueField x)).toLinearMap

/-- The action of the source stalk on `κ(x)` factors through the stalk of the
distinguished fibre point. -/
instance sourceStalkFiberStalkSourceResidueFieldIsScalarTower
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsScalarTower (X.presheaf.stalk x) (fiberStalkAt f x)
      (X.residueField x) := sorry

/-- The canonical map from the distinguished fibre stalk to `κ(x)` is
surjective. -/
theorem fiberStalkToSourceResidueField_surjective
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Function.Surjective (fiberStalkToSourceResidueField f x).hom := sorry

end AlgebraicGeometry.Scheme.Hom
