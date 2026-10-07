module

public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.Extension.Cotangent.Surjective
public import stacks_project.Chap90.Lemma_90_3_4_Length

/-!
# Comparison of kernel cotangents with first cotangent homology

For a ring map `Λ → k` to a field, write `k'` for `residueImage Λ k`. Surjectivity of
`Λ → k'` identifies the kernel cotangent with `H1Cotangent Λ k'`, and functoriality of
`H1Cotangent` supplies the comparison map to `H1Cotangent Λ k`. When `A → k` is a
surjective `Λ`-algebra map, the same functoriality supplies the arrow from
`H1Cotangent Λ k` to the kernel cotangent of `A → k`.
-/

@[expose] public section

open scoped TensorProduct
open Algebra.Extension

universe u v w

namespace Algebra.H1Cotangent

/-- The canonical surjective presentation of `residueImage Λ k` over `Λ`. -/
noncomputable abbrev residueImageExtension (Λ : Type u) (k : Type v)
    [CommRing Λ] [Field k] [Algebra Λ k] :
    Extension Λ (residueImage Λ k) :=
  Extension.ofSurjective (Algebra.ofId Λ (residueImage Λ k)) Ideal.Quotient.mk_surjective

/-- The kernel of the residue-image presentation is the kernel of `Λ → k'`. -/
theorem residueImageExtension_ker (Λ : Type u) (k : Type v)
    [CommRing Λ] [Field k] [Algebra Λ k] :
    (residueImageExtension Λ k).ker = RingHom.ker (algebraMap Λ (residueImage Λ k)) :=
  sorry

/-- The identification `H¹(L_{k'/Λ}) = m_Λ / m_Λ²` as `k'`-vector spaces, where
`k' = residueImage Λ k` and `m_Λ = ker (algebraMap Λ k)`. -/
noncomputable def kerCotangentEquiv (Λ : Type u) (k : Type v)
    [CommRing Λ] [Field k] [Algebra Λ k] :
    (RingHom.ker (algebraMap Λ k)).Cotangent ≃ₗ[residueImage Λ k]
      H1Cotangent Λ (residueImage Λ k) :=
  let h := (Ideal.Quotient.mk_surjective :
    Function.Surjective (algebraMap Λ (residueImage Λ k)))
  let e :=
    Ideal.Cotangent.equivOfEq (RingHom.ker (algebraMap Λ k))
      (residueImageExtension Λ k).ker
      (((congrArg RingHom.ker
            (Ideal.Quotient.algebraMap_eq (RingHom.ker (algebraMap Λ k)))).trans
          Ideal.mk_ker).symm)
  { toFun := fun x ↦ (equivOfSurjective h).symm (Extension.Cotangent.of (e x))
    invFun := fun y ↦
      e.symm (Extension.Cotangent.val (equivOfSurjective h y))
    map_add' := sorry
    map_smul' := sorry
    left_inv := sorry
    right_inv := sorry }

/-- The canonical comparison `m_Λ / m_Λ² ⟶ H¹(L_{k/Λ})`. -/
noncomputable def ofKerCotangent (Λ : Type u) (k : Type v)
    [CommRing Λ] [Field k] [Algebra Λ k] :
    (RingHom.ker (algebraMap Λ k)).Cotangent →ₗ[residueImage Λ k] H1Cotangent Λ k :=
  map Λ Λ (residueImage Λ k) k ∘ₗ (kerCotangentEquiv Λ k).toLinearMap

/-- The `k`-linear map induced by `ofKerCotangent` after base change along `k' → k`. -/
noncomputable def ofKerCotangentBaseChange (Λ : Type u) (k : Type v)
    [CommRing Λ] [Field k] [Algebra Λ k] :
    k ⊗[residueImage Λ k] (RingHom.ker (algebraMap Λ k)).Cotangent →ₗ[k]
      H1Cotangent Λ k :=
  (ofKerCotangent Λ k).liftBaseChange k

/-- When `Λ → k` is surjective, the kernel cotangent is identified with `H1Cotangent Λ k`
as modules over `residueImage Λ k`. -/
noncomputable def equivKerCotangent (Λ : Type u) (k : Type v)
    [CommRing Λ] [Field k] [Algebra Λ k]
    (h : Function.Surjective (algebraMap Λ k)) :
    (RingHom.ker (algebraMap Λ k)).Cotangent ≃ₗ[residueImage Λ k] H1Cotangent Λ k :=
  let P := Extension.ofSurjective (Algebra.ofId Λ k) h
  let e := Ideal.Cotangent.equivOfEq (RingHom.ker (algebraMap Λ k)) P.ker rfl
  { toFun := fun x ↦ (equivOfSurjective h).symm (Extension.Cotangent.of (e x))
    invFun := fun y ↦ e.symm (Extension.Cotangent.val (equivOfSurjective h y))
    map_add' := sorry
    map_smul' := sorry
    left_inv := sorry
    right_inv := sorry }

/-- The comparison `H¹(L_{k/Λ}) ⟶ m_A / m_A²` along a surjective `Λ`-algebra map `A → k`. -/
noncomputable def toKerCotangent (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [Field k]
    [Algebra Λ A] [Algebra Λ k] [Algebra A k] [IsScalarTower Λ A k]
    (h : Function.Surjective (algebraMap A k)) :
    H1Cotangent Λ k →ₗ[Λ] (RingHom.ker (algebraMap A k)).Cotangent where
  toFun x :=
    let P := Extension.ofSurjective (Algebra.ofId A k) h
    Ideal.Cotangent.equivOfEq P.ker (RingHom.ker (algebraMap A k)) rfl
      (P.cotangentEquivCotangentKer (equivOfSurjective h (map Λ A k k x)))
  map_add' := sorry
  map_smul' := sorry

/-- In a tower `Λ → A → k`, `ker (Λ → k)` lands in the comap of `ker (A → k)`. -/
theorem ker_le_comap_ker_of_tower (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra A k] [Algebra Λ k] [IsScalarTower Λ A k] :
    RingHom.ker (algebraMap Λ k) ≤
      (RingHom.ker (algebraMap A k)).comap (Algebra.ofId Λ A) :=
  sorry

/-- `kerCotangentEquiv` evaluates by transporting the presentation cotangent identification. -/
theorem kerCotangentEquiv_apply (Λ : Type u) (k : Type v)
    [CommRing Λ] [Field k] [Algebra Λ k]
    (x : (RingHom.ker (algebraMap Λ k)).Cotangent) :
    kerCotangentEquiv Λ k x =
      (equivOfSurjective (Ideal.Quotient.mk_surjective :
            Function.Surjective (algebraMap Λ (residueImage Λ k)))).symm
        (Extension.Cotangent.of
          (Ideal.Cotangent.equivOfEq (RingHom.ker (algebraMap Λ k))
            (residueImageExtension Λ k).ker
            (((congrArg RingHom.ker
                  (Ideal.Quotient.algebraMap_eq
                    (RingHom.ker (algebraMap Λ k)))).trans
                Ideal.mk_ker).symm) x)) :=
  sorry

/-- `ofKerCotangent` is functoriality of `H1Cotangent` after `kerCotangentEquiv`. -/
theorem ofKerCotangent_eq_map (Λ : Type u) (k : Type v)
    [CommRing Λ] [Field k] [Algebra Λ k] :
    ofKerCotangent Λ k =
      map Λ Λ (residueImage Λ k) k ∘ₗ (kerCotangentEquiv Λ k).toLinearMap :=
  sorry

/-- Base change of `ofKerCotangent` evaluates on elementary tensors by scaling. -/
theorem ofKerCotangentBaseChange_tmul (Λ : Type u) (k : Type v)
    [CommRing Λ] [Field k] [Algebra Λ k]
    (r : k) (x : (RingHom.ker (algebraMap Λ k)).Cotangent) :
    ofKerCotangentBaseChange Λ k (r ⊗ₜ x) = r • ofKerCotangent Λ k x :=
  sorry

/-- `equivKerCotangent` evaluates by transporting the presentation cotangent identification. -/
theorem equivKerCotangent_apply (Λ : Type u) (k : Type v)
    [CommRing Λ] [Field k] [Algebra Λ k]
    (h : Function.Surjective (algebraMap Λ k))
    (x : (RingHom.ker (algebraMap Λ k)).Cotangent) :
    equivKerCotangent Λ k h x =
      (equivOfSurjective h).symm
        (Extension.Cotangent.of
          (P := Extension.ofSurjective (Algebra.ofId Λ k) h) x) :=
  sorry

/-- Under surjectivity of `Λ → k`, `ofKerCotangent` agrees with `equivKerCotangent`
after transporting scalars along `residueImage Λ k ≃ₐ[Λ] k`. -/
theorem ofKerCotangent_eq_equivKerCotangent (Λ : Type u) (k : Type v)
    [CommRing Λ] [Field k] [Algebra Λ k]
    (h : Function.Surjective (algebraMap Λ k))
    (x : (RingHom.ker (algebraMap Λ k)).Cotangent) :
    equivKerCotangent Λ k h x = ofKerCotangent Λ k x :=
  sorry

/-- Under surjectivity of `Λ → k`, the canonical comparison map is bijective. -/
theorem bijective_ofKerCotangent_of_surjective (Λ : Type u) (k : Type v)
    [CommRing Λ] [Field k] [Algebra Λ k]
    (h : Function.Surjective (algebraMap Λ k)) :
    Function.Bijective (ofKerCotangent Λ k) :=
  sorry

/-- `toKerCotangent` evaluates as `cotangentEquivCotangentKer` after `equivOfSurjective`
and `H1Cotangent.map`. -/
theorem toKerCotangent_apply (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [Field k]
    [Algebra Λ A] [Algebra Λ k] [Algebra A k] [IsScalarTower Λ A k]
    (h : Function.Surjective (algebraMap A k)) (x : H1Cotangent Λ k) :
    toKerCotangent Λ A k h x =
      Ideal.Cotangent.equivOfEq
        (Extension.ofSurjective (Algebra.ofId A k) h).ker
        (RingHom.ker (algebraMap A k)) rfl
        ((Extension.ofSurjective (Algebra.ofId A k) h).cotangentEquivCotangentKer
          (equivOfSurjective h (map Λ A k k x))) :=
  sorry

end Algebra.H1Cotangent

