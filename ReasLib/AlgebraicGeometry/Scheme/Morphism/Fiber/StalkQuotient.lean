module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Stalk

/-!
# Local rings of scheme-theoretic fibres

The stalk of a scheme-theoretic fibre at the distinguished point determined by a
source point is canonically isomorphic to the quotient of the source stalk by
the extended maximal ideal of the target stalk, and to the residue-field tensor
product.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The extended maximal ideal `𝔪_{f(x)} 𝒪_{X, x}` of the source stalk. -/
abbrev sourceStalkBaseMaximalIdeal {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Ideal (X.presheaf.stalk x) :=
  (maximalIdeal (S.presheaf.stalk (f x))).map (f.stalkMap x).hom

/-- The quotient `𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}`. -/
abbrev sourceStalkQuotient {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Type u :=
  X.presheaf.stalk x ⧸ sourceStalkBaseMaximalIdeal f x

/-- The quotient `𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}` is a local ring. -/
noncomputable instance instIsLocalRing_sourceStalkQuotient
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsLocalRing (sourceStalkQuotient f x) :=
  @IsLocalRing.of_surjective' _ _ _ _ _
    (Ideal.Quotient.nontrivial_iff.mpr
      (IsLocalRing.map_maximalIdeal_lt_top (f.stalkMap x).hom).ne)
    (Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x))
    (Ideal.Quotient.mk_surjective)

/-- The tensor product `𝒪_{X, x} ⊗_{𝒪_{S, f(x)}} κ(f(x))`. -/
abbrev sourceStalkTensorResidueField {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Type u :=
  X.presheaf.stalk x ⊗[S.presheaf.stalk (f x)] S.residueField (f x)

/-- The canonical map `𝒪_{S, f(x)} → 𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}` kills the
maximal ideal of the target stalk. -/
theorem algebraMap_sourceStalkQuotient_eq_zero_of_mem_maximalIdeal
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (r : S.presheaf.stalk (f x)) (hr : r ∈ maximalIdeal (S.presheaf.stalk (f x))) :
    ((Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x)).comp (f.stalkMap x).hom) r = 0 :=
  sorry

/-- The induced ring homomorphism `κ(f(x)) → 𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}`. -/
noncomputable def residueFieldToSourceStalkQuotient {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) :
    S.residueField (f x) →+* sourceStalkQuotient f x :=
  Ideal.Quotient.lift (maximalIdeal (S.presheaf.stalk (f x)))
    ((Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x)).comp (f.stalkMap x).hom)
    (algebraMap_sourceStalkQuotient_eq_zero_of_mem_maximalIdeal f x)

/-- The induced map sends the residue of a target-stalk element to the class of
its image in the source stalk. -/
theorem residueFieldToSourceStalkQuotient_residue {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (r : S.presheaf.stalk (f x)) :
    residueFieldToSourceStalkQuotient f x ((S.residue (f x)).hom r) =
      Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x) ((f.stalkMap x).hom r) :=
  sorry

/-- The morphism `Spec(𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}) ⟶ X` induced by the
quotient of the source stalk. -/
noncomputable def fromSpecSourceStalkQuotient {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Spec (CommRingCat.of (sourceStalkQuotient f x)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x))) ≫
    X.fromSpecStalk x

/-- The morphism `Spec(𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}) ⟶ Spec κ(f(x))` induced
by the residue-field action on the quotient. -/
noncomputable def fromSpecSourceStalkQuotientToSpecResidueField {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) :
    Spec (CommRingCat.of (sourceStalkQuotient f x)) ⟶ Spec (S.residueField (f x)) :=
  Spec.map (CommRingCat.ofHom (residueFieldToSourceStalkQuotient f x))

/-- The quotient spectrum sits over both `X` and `Spec κ(f(x))` in a commuting
square. -/
theorem fromSpecSourceStalkQuotient_fac {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    fromSpecSourceStalkQuotient f x ≫ f =
      fromSpecSourceStalkQuotientToSpecResidueField f x ≫
        S.fromSpecResidueField (f x) := sorry

/-- The induced morphism from `Spec(𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x})` to the
scheme-theoretic fibre `X_{f(x)}`. -/
noncomputable def fromSpecSourceStalkQuotientToFiber {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) :
    Spec (CommRingCat.of (sourceStalkQuotient f x)) ⟶ f.fiber (f x) :=
  pullback.lift (fromSpecSourceStalkQuotient f x)
    (fromSpecSourceStalkQuotientToSpecResidueField f x)
    (fromSpecSourceStalkQuotient_fac f x)

/-- The closed point of the quotient spectrum is sent to the distinguished
fibre point `f.asFiber x`. -/
theorem fromSpecSourceStalkQuotientToFiber_asFiber {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) :
    fromSpecSourceStalkQuotientToFiber f x
        (closedPoint (CommRingCat.of (sourceStalkQuotient f x))) =
      f.asFiber x := sorry

/-- The structure map `𝒪_{X, x} → 𝒪_{X_{f(x)}, x}` kills the extended
maximal ideal `𝔪_{f(x)} 𝒪_{X, x}`. -/
theorem sourceStalkToFiberStalk_eq_zero_of_mem_map {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (a : X.presheaf.stalk x) (ha : a ∈ sourceStalkBaseMaximalIdeal f x) :
    (sourceStalkToFiberStalk f x).hom a = 0 := sorry

/-- The induced map `𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x} → 𝒪_{X_{f(x)}, x}` from
the fibre inclusion on stalks. -/
noncomputable def sourceStalkQuotientToFiberStalk {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) :
    sourceStalkQuotient f x →+* fiberStalkAt f x :=
  Ideal.Quotient.lift (sourceStalkBaseMaximalIdeal f x) (sourceStalkToFiberStalk f x).hom
    (sourceStalkToFiberStalk_eq_zero_of_mem_map f x)

/-- The induced quotient map sends the class of a source-stalk element to its
image under the fibre-inclusion stalk map. -/
theorem sourceStalkQuotientToFiberStalk_mk {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (a : X.presheaf.stalk x) :
    sourceStalkQuotientToFiberStalk f x
        (Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x) a) =
      (sourceStalkToFiberStalk f x).hom a := sorry

/-- The local homomorphism `𝒪_{X_{f(x)}, x} → 𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}`
induced by the morphism from the quotient spectrum to the fibre. -/
noncomputable def fiberStalkAtToSourceStalkQuotient {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) :
    fiberStalkAt f x ⟶ CommRingCat.of (sourceStalkQuotient f x) :=
  ((f.fiber (f x)).presheaf.stalkCongr
      (Inseparable.of_eq (fromSpecSourceStalkQuotientToFiber_asFiber f x).symm)).hom ≫
    Scheme.stalkClosedPointTo (fromSpecSourceStalkQuotientToFiber f x)

/-- The two comparison maps between the fibre stalk and the source-stalk
quotient are inverse on the quotient. -/
theorem fiberStalkAtToSourceStalkQuotient_comp_toFiberStalk {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) :
    (fiberStalkAtToSourceStalkQuotient f x).hom.comp
        (sourceStalkQuotientToFiberStalk f x) =
      RingHom.id (sourceStalkQuotient f x) := sorry

/-- The two comparison maps between the fibre stalk and the source-stalk
quotient are inverse on the fibre stalk. -/
theorem sourceStalkQuotientToFiberStalk_comp_toQuotient {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) :
    (sourceStalkQuotientToFiberStalk f x).comp
        (fiberStalkAtToSourceStalkQuotient f x).hom =
      RingHom.id (fiberStalkAt f x) := sorry

/-- The stalk of the scheme-theoretic fibre at the distinguished point is
isomorphic to the quotient of the source stalk by the extended maximal ideal. -/
noncomputable def fiberStalkAtEquivQuotient {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    fiberStalkAt f x ≃+* sourceStalkQuotient f x :=
  RingEquiv.ofRingHom (fiberStalkAtToSourceStalkQuotient f x).hom
    (sourceStalkQuotientToFiberStalk f x)
    (fiberStalkAtToSourceStalkQuotient_comp_toFiberStalk f x)
    (sourceStalkQuotientToFiberStalk_comp_toQuotient f x)

/-- The fibre-stalk quotient isomorphism identifies the fibre-inclusion stalk
map with the quotient map. -/
theorem fiberStalkAtEquivQuotient_symm_mk {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (a : X.presheaf.stalk x) :
    (fiberStalkAtEquivQuotient f x).symm
        (Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x) a) =
      (sourceStalkToFiberStalk f x).hom a := sorry

/-- The quotient `𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}` is isomorphic to the
residue-field tensor product `𝒪_{X, x} ⊗_{𝒪_{S, f(x)}} κ(f(x))`. -/
noncomputable def sourceStalkQuotientEquivTensor {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) :
    sourceStalkQuotient f x ≃+* sourceStalkTensorResidueField f x :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (X.presheaf.stalk x)
      (maximalIdeal (S.presheaf.stalk (f x)))).toRingEquiv

/-- The stalk of the scheme-theoretic fibre at the distinguished point is
isomorphic to the residue-field tensor product of the source stalk. -/
noncomputable def fiberStalkAtEquivTensor {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    fiberStalkAt f x ≃+* sourceStalkTensorResidueField f x :=
  (fiberStalkAtEquivQuotient f x).trans (sourceStalkQuotientEquivTensor f x)

end AlgebraicGeometry.Scheme.Hom
