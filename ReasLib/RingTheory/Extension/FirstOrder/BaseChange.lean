module

public import ReasLib.RingTheory.Extension.FirstOrder
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base Change of Universal First-Order Thickenings

The base change is Mathlib's canonical `Extension.baseChange`.  This leaf owns
only preservation of the universal property; localization of the base ring is
a specialization.

@stack 04EE
-/

@[expose] public section

noncomputable section

open Algebra

universe u v w x y

namespace Algebra.Extension

variable {R : Type u} {S : Type v} {T : Type x}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable {P : Extension.{w} R S}

/-- The structure map of a base-changed extension is the tensor product of the identity with
the original structure map. -/
@[simp]
theorem baseChange_toAlgHom :
    IsScalarTower.toAlgHom T (P.baseChange (T := T)).Ring (TensorProduct R T S) =
      Algebra.TensorProduct.map (AlgHom.id T T)
        (IsScalarTower.toAlgHom R P.Ring S) :=
  rfl

namespace FirstOrder.IsUniversal

/-- Universal first-order thickenings are preserved by arbitrary base change.

For a localization `T` of `R`, this is the owner-level form of base-ring
localization in Stacks, Lemma 10.149.4 (1). -/
@[stacks 04EE "(1), base change of a universal first-order thickening"]
theorem baseChange (hP : IsUniversal.{y} P) :
    IsUniversal.{y} (P.baseChange (T := T)) := by
  refine ⟨?_, ?_⟩
  · set_option backward.isDefEq.respectTransparency false in
    rw [P.ker_baseChange T, ← Ideal.map_pow, hP.squareZero, Ideal.map_bot]
  · intro A _ _ I hI f
    -- Proof-local instance justification (explicit-map choice): the `R`-action on this test
    -- algebra must be the composite through `T`. The endpoint rings alone do not determine that
    -- choice, so registering it globally would create an instance diamond.
    letI : Algebra R A :=
      ((algebraMap T A).comp (algebraMap R T)).toAlgebra
    letI : IsScalarTower R T A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let fR : S →ₐ[R] A ⧸ I :=
      (f.restrictScalars R).comp Algebra.TensorProduct.includeRight
    obtain ⟨gR, hgR, huniqR⟩ := hP.existsUniqueLiftAt I hI fR
    let e := AlgHom.liftEquiv R T P.Ring A
    let g : (P.baseChange (T := T)).Ring →ₐ[T] A := e gR
    refine ⟨g, ?_, ?_⟩
    · apply Algebra.TensorProduct.ext_ring
      convert hgR using 1
      · ext p
        change Ideal.Quotient.mk I
            ((AlgHom.liftEquiv R T P.Ring A) gR (1 ⊗ₜ[R] p)) =
          Ideal.Quotient.mk I (gR p)
        simp
      · ext p
        change f
            ((Algebra.TensorProduct.map (AlgHom.id T T)
              (IsScalarTower.toAlgHom R P.Ring S)) (1 ⊗ₜ[R] p)) =
          f (Algebra.TensorProduct.includeRight (algebraMap P.Ring S p))
        simp
    · intro q hq
      let qR : P.Ring →ₐ[R] A := e.symm q
      have hqR :
          (Ideal.Quotient.mkₐ R I).comp qR =
            fR.comp (IsScalarTower.toAlgHom R P.Ring S) := by
        apply AlgHom.ext
        intro p
        change ((Ideal.Quotient.mkₐ T I).comp q)
            (Algebra.TensorProduct.includeRight p) =
          (f.comp (IsScalarTower.toAlgHom T
            (P.baseChange (T := T)).Ring (TensorProduct R T S)))
            (Algebra.TensorProduct.includeRight p)
        exact DFunLike.congr_fun hq (Algebra.TensorProduct.includeRight p)
      have hqg := huniqR qR hqR
      apply e.symm.injective
      simpa [qR, g] using hqg

end FirstOrder.IsUniversal

end Algebra.Extension
