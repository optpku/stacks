/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.AlgebraicGeometry.Birational.RationalMap

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

namespace RationalFunction

/-- A dense open index of a scheme is a dense open subscheme, ordered by reverse inclusion. -/
abbrev DenseOpenIndex (X : Scheme.{u}) :=
  OrderDual { U : X.Opens // Dense (U : Set X) }

/-- The whole scheme is a dense open index. -/
instance (X : Scheme.{u}) : Nonempty (DenseOpenIndex X) :=
  ⟨⟨⊤, dense_univ⟩⟩

/-- Dense open indices are directed under reverse inclusion, using intersections. -/
instance (X : Scheme.{u}) : IsDirectedOrder (DenseOpenIndex X) where
  directed U V :=
    ⟨⟨U.1 ⊓ V.1, U.2.inter_of_isOpen_left V.2 U.1.isOpen⟩,
      (show (U.1 ⊓ V.1) ≤ U.1 from inf_le_left),
      (show (U.1 ⊓ V.1) ≤ V.1 from inf_le_right)⟩

/-- The ring of sections on a dense open index. -/
abbrev sections (X : Scheme.{u}) (U : DenseOpenIndex X) := Γ(X, U.1)

/-- Restriction of sections along reverse inclusion of dense open indices. -/
def restriction (X : Scheme.{u}) (U V : DenseOpenIndex X) (h : U ≤ V) :
    sections X U →+* sections X V :=
  (X.presheaf.map (homOfLE h).op).hom

/-- The ring of rational functions as the direct limit of section rings over dense opens. -/
abbrev carrier (X : Scheme.{u}) :=
  Ring.DirectLimit (fun U : DenseOpenIndex X ↦ sections X U)
    fun (U V : DenseOpenIndex X) h ↦
      (restriction X U V h : sections X U → sections X V)

/-- Insert a section on a dense open subset into the ring of rational functions. -/
def stage (X : Scheme.{u}) (U : DenseOpenIndex X) : sections X U →+* carrier X :=
  Ring.DirectLimit.of (fun V : DenseOpenIndex X ↦ sections X V)
    (fun (U V : DenseOpenIndex X) h ↦
      (restriction X U V h : sections X U → sections X V)) U

/-- Every rational function is represented by a section on some dense open subset. -/
theorem exists_rep (X : Scheme.{u}) (f : carrier X) :
    ∃ (U : DenseOpenIndex X) (s : sections X U), stage X U s = f :=
  Ring.DirectLimit.exists_of f

/-- The polynomial ring defining the affine line, lifted to the universe of the scheme. -/
abbrev AffineLineRing := ULift.{u} (Polynomial ℤ)

/-- The coordinate of the universe-lifted affine line. -/
def coordinate : AffineLineRing.{u} :=
  (ULift.ringEquiv : AffineLineRing.{u} ≃+* Polynomial ℤ).symm Polynomial.X

/-- Evaluation at a section, viewed as a map out of the universe-lifted polynomial ring. -/
def evalAt {X : Scheme.{u}} {U : DenseOpenIndex X} (s : sections X U) :
    AffineLineRing.{u} →+* sections X U :=
  (Polynomial.eval₂RingHom (Int.castRingHom _) s).comp
    (ULift.ringEquiv : AffineLineRing.{u} ≃+* Polynomial ℤ).toRingHom

/-- The structure map from the universe-lifted integers to the universe-lifted polynomial ring. -/
def polynomialC : ULift.{u} ℤ →+* AffineLineRing.{u} :=
  (ULift.ringEquiv : AffineLineRing.{u} ≃+* Polynomial ℤ).symm.toRingHom.comp
    ((Polynomial.C : ℤ →+* Polynomial ℤ).comp
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom)

/-- A section on a dense open subset determines a partial map to the affine line. -/
def partialMap (X : Scheme.{u}) (U : DenseOpenIndex X) (s : sections X U) :
    X.PartialMap (Spec (CommRingCat.of AffineLineRing.{u})) where
  domain := U.1
  dense_domain := U.2
  hom := U.1.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (evalAt s))

end RationalFunction

/-- The type of rational functions on a scheme. -/
abbrev RationalFunction (X : Scheme.{u}) := RationalFunction.carrier X

/-- The commutative ring of rational functions on a scheme. -/
abbrev rationalFunctionRing (X : Scheme.{u}) : CommRingCat.{u} :=
  CommRingCat.of (RationalFunction X)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- The scoped notation for the ring of rational functions on a scheme. -/
scoped notation "R(" X ")" => Scheme.rationalFunctionRing X

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The rational-function ring is the direct limit of section rings over dense open subsets. -/
theorem rationalFunctionRing_def (X : Scheme.{u}) :
    rationalFunctionRing X = CommRingCat.of (RationalFunction X) :=
  rfl

/-- Extract the rational function represented by a partial map to the affine line. -/
def PartialMap.toRationalFunction
    (f : X.PartialMap (Spec (CommRingCat.of RationalFunction.AffineLineRing.{u}))) :
    RationalFunction X :=
  RationalFunction.stage X ⟨f.domain, f.dense_domain⟩
    (f.domain.topIso.hom (f.hom.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of RationalFunction.AffineLineRing.{u})).inv
        RationalFunction.coordinate)))

/-- Equivalent partial maps to the affine line determine the same rational function. -/
theorem PartialMap.toRationalFunction_eq_of_equiv
    {f g : X.PartialMap (Spec (CommRingCat.of RationalFunction.AffineLineRing.{u}))}
    (h : f.equiv g) :
    f.toRationalFunction = g.toRationalFunction := sorry

/-- Extract the rational function represented by a rational map to the affine line. -/
def RationalMap.toRationalFunction
    (f : X.RationalMap (Spec (CommRingCat.of RationalFunction.AffineLineRing.{u}))) :
    RationalFunction X :=
  Quotient.lift PartialMap.toRationalFunction
    (fun _ _ h ↦ PartialMap.toRationalFunction_eq_of_equiv h) f

namespace RationalFunction

/-- Send a rational function to the rational map represented by a chosen dense-open section. -/
def toRationalMap (X : Scheme.{u}) (f : RationalFunction X) :
    X.RationalMap (Spec (CommRingCat.of AffineLineRing.{u})) :=
  (partialMap X (exists_rep X f).choose (exists_rep X f).choose_spec.choose).toRationalMap

end RationalFunction

/-- Converting a rational function to a rational map and back is the identity. -/
theorem rationalFunctionRingEquivRationalMap_left_inv (X : Scheme.{u})
    (f : RationalFunction X) :
    RationalMap.toRationalFunction (RationalFunction.toRationalMap X f) = f := sorry

/-- Converting a rational map to a rational function and back is the identity. -/
theorem rationalFunctionRingEquivRationalMap_right_inv (X : Scheme.{u})
    (f : X.RationalMap (Spec (CommRingCat.of RationalFunction.AffineLineRing.{u}))) :
    RationalFunction.toRationalMap X f.toRationalFunction = f := sorry

/-- Rational functions are equivalently rational maps to the affine line `Spec ℤ[t]`. -/
def rationalFunctionRingEquivRationalMap (X : Scheme.{u}) :
    rationalFunctionRing X ≃
      X.RationalMap (Spec (CommRingCat.of RationalFunction.AffineLineRing.{u})) where
  toFun := RationalFunction.toRationalMap X
  invFun := RationalMap.toRationalFunction
  left_inv := rationalFunctionRingEquivRationalMap_left_inv X
  right_inv := rationalFunctionRingEquivRationalMap_right_inv X

/-- Ring homomorphisms from the universe-lifted `ℤ[t]` are determined by the image of `t`. -/
def polynomialRingHomEquiv (K : Type u) [CommRing K] :
    (CommRingCat.of RationalFunction.AffineLineRing.{u} ⟶ CommRingCat.of K) ≃ K where
  toFun f := f RationalFunction.coordinate
  invFun x := CommRingCat.ofHom ((Polynomial.eval₂RingHom (Int.castRingHom K) x).comp
    (ULift.ringEquiv : RationalFunction.AffineLineRing.{u} ≃+* Polynomial ℤ).toRingHom)
  left_inv f := by
    apply CommRingCat.hom_ext
    rw [← RingHom.cancel_right
      (f := (ULift.ringEquiv : RationalFunction.AffineLineRing.{u} ≃+* Polynomial ℤ).symm.toRingHom)
      (hf := ULift.ringEquiv.symm.surjective)]
    apply Polynomial.ringHom_ext
    · intro z
      simp
    · simp [RationalFunction.coordinate]
  right_inv x := by simp [RationalFunction.coordinate]

/-- Every rational map to `Spec ℤ[t]`, followed by its structure map, is the canonical
map to `Spec ℤ`. -/
theorem rationalMap_comp_polynomialC (X : Scheme.{u})
    (f : X.RationalMap (Spec (CommRingCat.of RationalFunction.AffineLineRing.{u}))) :
    f.compHom (Spec.map (CommRingCat.ofHom RationalFunction.polynomialC)) =
      (specULiftZIsTerminal.from X).toRationalMap := by
  obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjective f
  rw [← RationalMap.compHom_toRationalMap]
  apply PartialMap.toRationalMap_eq_iff.mpr
  exact ⟨f.domain, f.dense_domain, le_rfl, le_top, specULiftZIsTerminal.hom_ext _ _⟩

/-- Every morphism to `Spec ℤ[t]`, followed by its structure map, is the canonical map to
`Spec ℤ`. -/
theorem hom_comp_polynomialC (X : Scheme.{u}) [IsIntegral X]
    (f : Spec X.functionField ⟶
      Spec (CommRingCat.of RationalFunction.AffineLineRing.{u})) :
    f ≫ Spec.map (CommRingCat.ofHom RationalFunction.polynomialC) =
      X.fromSpecStalk (genericPoint X) ≫ specULiftZIsTerminal.from X :=
  specULiftZIsTerminal.hom_ext _ _

/-- For an integral scheme, rational maps to `Spec ℤ[t]` are equivalent to elements of its
function field. -/
def rationalMapEquivFunctionField (X : Scheme.{u}) [IsIntegral X] :
    X.RationalMap (Spec (CommRingCat.of RationalFunction.AffineLineRing.{u})) ≃
      X.functionField := by
  let sX : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) := specULiftZIsTerminal.from X
  let sY : Spec (CommRingCat.of RationalFunction.AffineLineRing.{u}) ⟶
      Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    Spec.map (CommRingCat.ofHom RationalFunction.polynomialC)
  let hY : LocallyOfFiniteType sY :=
    HasRingHomProperty.Spec_iff.mpr <| by
      apply RingHom.FiniteType.comp
      · exact RingHom.FiniteType.of_surjective _ ULift.ringEquiv.symm.surjective
      · apply RingHom.FiniteType.comp
        · have hC : (Polynomial.C : ℤ →+* Polynomial ℤ) =
              algebraMap ℤ (Polynomial ℤ) :=
            RingHom.ext fun z ↦ Polynomial.C_eq_algebraMap z
          rw [hC, RingHom.finiteType_algebraMap]
          infer_instance
        · exact RingHom.FiniteType.of_surjective _ ULift.ringEquiv.surjective
  exact
    (Equiv.subtypeUnivEquiv (rationalMap_comp_polynomialC X)).symm |>.trans
      ((@RationalMap.equivFunctionField _ _ _ sX sY _ hY).symm) |>.trans
      (Equiv.subtypeUnivEquiv (hom_comp_polynomialC X)) |>.trans
      Spec.homEquiv |>.trans (polynomialRingHomEquiv X.functionField)

/-- The underlying equivalence between rational functions and the function field of an integral
scheme. -/
def rationalFunctionEquivFunctionField (X : Scheme.{u}) [IsIntegral X] :
    rationalFunctionRing X ≃ X.functionField :=
  (rationalFunctionRingEquivRationalMap X).trans (rationalMapEquivFunctionField X)

/-- The rational-function/function-field equivalence preserves addition. -/
theorem rationalFunctionRing_equiv_functionField_map_add
    (X : Scheme.{u}) [IsIntegral X] (f g : rationalFunctionRing X) :
    rationalFunctionEquivFunctionField X (f + g) =
      rationalFunctionEquivFunctionField X f + rationalFunctionEquivFunctionField X g := sorry

/-- The rational-function/function-field equivalence preserves multiplication. -/
theorem rationalFunctionRing_equiv_functionField_map_mul
    (X : Scheme.{u}) [IsIntegral X] (f g : rationalFunctionRing X) :
    rationalFunctionEquivFunctionField X (f * g) =
      rationalFunctionEquivFunctionField X f * rationalFunctionEquivFunctionField X g := sorry

/-- For an integral scheme, its rational-function ring is canonically its function field. -/
def rationalFunctionRing_equiv_functionField (X : Scheme.{u}) [IsIntegral X] :
    rationalFunctionRing X ≃+* X.functionField :=
  { rationalFunctionEquivFunctionField X with
    map_add' := rationalFunctionRing_equiv_functionField_map_add X
    map_mul' := rationalFunctionRing_equiv_functionField_map_mul X }

end AlgebraicGeometry.Scheme
