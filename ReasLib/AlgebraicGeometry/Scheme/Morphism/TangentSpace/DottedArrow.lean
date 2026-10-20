module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.RingTheory.DualNumber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.DualNumber

/-!
# Dotted-arrow tangent spaces

This leaf identifies dual-number lifts of a point over a scheme morphism with
the relative-derivation model of its tangent space and transports the canonical
vector-space structure across that identification.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DualNumber

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A dotted tangent arrow at `x` over `f : X ⟶ S` is a morphism from the
dual-number spectrum to `X` whose closed point is `x` and whose composite with
`f` is the canonical dual-number point over `f x`. -/
def DottedTangentArrow {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :=
  { θ : Spec (CommRingCat.of ((X.residueField x)[ε])) ⟶ X //
    dualNumberPointInclusion x ≫ θ = X.fromSpecResidueField x ∧
      θ ≫ f = dualNumberToBasePoint f x ≫ S.fromSpecResidueField (f x) }

/-- Dotted tangent arrows at `x` are canonically equivalent to relative
derivations from `𝒪_{X,x}` to `κ(x)` over `𝒪_{S,f(x)}`. -/
noncomputable def dottedTangentArrowEquiv {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    DottedTangentArrow f x ≃ tangentSpaceAt f x where
  toFun θ :=
    let p := SpecToEquivOfLocalRing X
      (CommRingCat.of ((X.residueField x)[ε])) θ.1
    let hp : p.1 = x := by
      let q : (X.residueField x)[ε] →+* X.residueField x :=
        (TrivSqZeroExt.fstHom (X.residueField x) (X.residueField x)
          (X.residueField x)).toRingHom
      let hq : IsLocalHom q :=
        IsLocalHom.of_surjective q fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩
      have hclosed :
          dualNumberPointInclusion x
              (IsLocalRing.closedPoint (CommRingCat.of (X.residueField x))) =
            IsLocalRing.closedPoint
              (CommRingCat.of ((X.residueField x)[ε])) := by
        simpa [dualNumberPointInclusion, q] using
          (@Spec_closedPoint (CommRingCat.of ((X.residueField x)[ε]))
            (CommRingCat.of (X.residueField x)) _ _ (CommRingCat.ofHom q) hq)
      have h := congrArg
        (fun g ↦ g (IsLocalRing.closedPoint (CommRingCat.of (X.residueField x)))) θ.2.1
      change θ.1 (IsLocalRing.closedPoint
        (CommRingCat.of ((X.residueField x)[ε]))) = x
      rw [Scheme.Hom.comp_apply, hclosed] at h
      exact h.trans (Scheme.fromSpecResidueField_apply x _)
    let φ : X.presheaf.stalk x →+* (X.residueField x)[ε] :=
      ((X.presheaf.stalkCongr (.of_eq hp.symm)).hom ≫ p.2.1).hom
    let algebraSource : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    let algebraResidue : Algebra (X.presheaf.stalk x) (X.residueField x) :=
      (X.residue x).hom.toAlgebra
    let algebraBaseResidue : Algebra (S.presheaf.stalk (f x)) (X.residueField x) :=
      ((X.residue x).hom.comp (f.stalkMap x).hom).toAlgebra
    @Derivation.mk (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (X.residueField x) _ _ _ algebraSource
      (@Algebra.toModule (X.presheaf.stalk x) (X.residueField x) _ _ algebraResidue)
      (@Algebra.toModule (S.presheaf.stalk (f x)) (X.residueField x) _ _
        algebraBaseResidue)
      (@LinearMap.mk (S.presheaf.stalk (f x)) (S.presheaf.stalk (f x)) _ _
        (RingHom.id (S.presheaf.stalk (f x))) (X.presheaf.stalk x) (X.residueField x) _ _
        (@Algebra.toModule (S.presheaf.stalk (f x)) (X.presheaf.stalk x) _ _ algebraSource)
        (@Algebra.toModule (S.presheaf.stalk (f x)) (X.residueField x) _ _
          algebraBaseResidue)
        (@AddHom.mk (X.presheaf.stalk x) (X.residueField x) _ _
          (fun a ↦ (φ a).snd) (by sorry))
        (by sorry))
      (by sorry) (by sorry)
  invFun d :=
    let φ : X.presheaf.stalk x →+* (X.residueField x)[ε] :=
      { toFun := fun a ↦ ⟨X.residue x a, d a⟩
        map_one' := by sorry
        map_mul' := by sorry
        map_zero' := by sorry
        map_add' := by sorry }
    let θ := (SpecToEquivOfLocalRing X
      (CommRingCat.of ((X.residueField x)[ε]))).symm
        ⟨x, ⟨CommRingCat.ofHom φ, by sorry⟩⟩
    ⟨θ, by sorry, by sorry⟩
  left_inv := by sorry
  right_inv := by sorry

/-- The additive commutative group structure on dotted tangent arrows obtained
from their canonical equivalence with relative derivations. -/
noncomputable instance dottedTangentArrowAddCommGroup
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    AddCommGroup (DottedTangentArrow f x) :=
  (dottedTangentArrowEquiv f x).addCommGroup

/-- The residue-field module structure on dotted tangent arrows obtained from
their canonical equivalence with the relative tangent space. -/
@[stacks 0B2B, instance]
noncomputable instance dottedTangentArrowModule
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Module (X.residueField x) (DottedTangentArrow f x) :=
  Equiv.module (X.residueField x) (dottedTangentArrowEquiv f x)

/-- The canonical identification of dotted tangent arrows with relative
derivations is linear over the residue field. -/
noncomputable def dottedTangentArrowLinearEquiv
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    DottedTangentArrow f x ≃ₗ[X.residueField x] tangentSpaceAt f x :=
  Equiv.linearEquiv (X.residueField x) (dottedTangentArrowEquiv f x)

end AlgebraicGeometry.Scheme.Hom
