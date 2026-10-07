module

public import Mathlib.RingTheory.Extension.ExtendScalars
public import ReasLib.RingTheory.Kaehler.BaseChange

/-!
# Extended Conormal Sequences

Surjections onto a common algebra give canonical linear maps from first
cotangent homology to kernel cotangents and from kernel cotangents to tensor
products of Kähler differentials. These maps form exact sequences and are
natural in compatible algebra towers.
-/

@[expose] public section

open Algebra Algebra.Extension KaehlerDifferential
open scoped TensorProduct

universe u v w x

noncomputable section

namespace Algebra.H1Cotangent

/-- The canonical map from first cotangent homology to the cotangent module
of a surjective algebra map in a compatible tower. -/
def toKerCotangent (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra Λ k] [Algebra A k] [IsScalarTower Λ A k]
    (h : Function.Surjective (algebraMap A k)) :
    H1Cotangent Λ k →ₗ[k] (Extension.ofSurjective (Algebra.ofId A k) h).Cotangent :=
  by
    let h' : Function.Surjective (Algebra.ofId A k) := by
      intro y
      rcases h y with ⟨x, hx⟩
      exact ⟨x, hx⟩
    change H1Cotangent Λ k →ₗ[k] (Extension.ofSurjective (Algebra.ofId A k) h').Cotangent
    exact (Extension.ofSurjective (Algebra.ofId A k) h').h1CotangentEquivCotangent.toLinearMap.comp
      (map Λ A k k)

/-- The canonical map to a kernel cotangent is the composite of the
cotangent-homology map and the surjective-presentation equivalence. -/
theorem toKerCotangent_apply (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra Λ k] [Algebra A k] [IsScalarTower Λ A k]
    (h : Function.Surjective (algebraMap A k)) (x : H1Cotangent Λ k) :
    toKerCotangent Λ A k h x =
      (Extension.ofSurjective (Algebra.ofId A k) h).h1CotangentEquivCotangent
        (map Λ A k k x) := sorry

/-- The map on kernel cotangents induced by an algebra map between
compatible surjections onto a common algebra. -/
def kerCotangentMap (B : Type u) (A : Type v) (k : Type w)
    [CommRing B] [CommRing A] [CommRing k]
    [Algebra B A] [Algebra A k] [Algebra B k] [IsScalarTower B A k]
    (hB : Function.Surjective (algebraMap B k))
    (hA : Function.Surjective (algebraMap A k)) :
    (Extension.ofSurjective (Algebra.ofId B k) hB).Cotangent →ₗ[k]
      (Extension.ofSurjective (Algebra.ofId A k) hA).Cotangent :=
  by
    let hB' : Function.Surjective (Algebra.ofId B k) := by
      intro y
      rcases hB y with ⟨x, hx⟩
      exact ⟨x, hx⟩
    let hA' : Function.Surjective (Algebra.ofId A k) := by
      intro y
      rcases hA y with ⟨x, hx⟩
      exact ⟨x, hx⟩
    change (Extension.ofSurjective (Algebra.ofId B k) hB').Cotangent →ₗ[k]
      (Extension.ofSurjective (Algebra.ofId A k) hA').Cotangent
    exact Cotangent.map
      (R := B) (S := k) (R' := A) (S' := k)
      (P := Extension.ofSurjective (Algebra.ofId B k) hB')
      (P' := Extension.ofSurjective (Algebra.ofId A k) hA')
      { toRingHom := by
          change B →+* A
          exact algebraMap B A
        toRingHom_algebraMap := by
          intro element
          change algebraMap B A (algebraMap B B element) =
            algebraMap A A (algebraMap B A element)
          simp
        algebraMap_toRingHom := by
          intro element
          change algebraMap A k (algebraMap B A element) = algebraMap B k element
          exact (IsScalarTower.algebraMap_apply B A k element).symm }

/-- The induced kernel-cotangent map sends the class of a kernel element
to the class of its image under the algebra map. -/
theorem kerCotangentMap_toCotangent (B : Type u) (A : Type v) (k : Type w)
    [CommRing B] [CommRing A] [CommRing k]
    [Algebra B A] [Algebra A k] [Algebra B k] [IsScalarTower B A k]
    (hB : Function.Surjective (algebraMap B k))
    (hA : Function.Surjective (algebraMap A k))
    (x : B) (hx : x ∈ RingHom.ker (algebraMap B k))
    (hxA : algebraMap B A x ∈ RingHom.ker (algebraMap A k)) :
    kerCotangentMap B A k hB hA (Cotangent.of (Ideal.toCotangent _ ⟨x, hx⟩)) =
      Cotangent.of (Ideal.toCotangent _ ⟨algebraMap B A x, hxA⟩) := sorry

/-- The canonical maps from first cotangent homology to kernel cotangents
commute with the map induced by compatible surjections onto a common algebra. -/
@[stacks 06S8]
theorem toKerCotangent_naturality (Λ : Type u) (B : Type v) (A : Type w) (k : Type x)
    [CommRing Λ] [CommRing B] [CommRing A] [CommRing k]
    [Algebra Λ B] [Algebra Λ A] [Algebra Λ k]
    [Algebra B A] [Algebra B k] [Algebra A k]
    [IsScalarTower Λ B A] [IsScalarTower Λ B k] [IsScalarTower Λ A k] [IsScalarTower B A k]
    (hB : Function.Surjective (algebraMap B k))
    (hA : Function.Surjective (algebraMap A k)) :
    kerCotangentMap B A k hB hA ∘ₗ toKerCotangent Λ B k hB = toKerCotangent Λ A k hA := sorry

end Algebra.H1Cotangent

namespace KaehlerDifferential

/-- The conormal map of a surjection, linear over its target algebra,
obtained from the kernel-cotangent differential by extending scalars. -/
def kerCotangentToTensor_extend (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra A k]
    (h : Function.Surjective (algebraMap A k)) :
    (Extension.ofSurjective (Algebra.ofId A k) h).Cotangent →ₗ[k] k ⊗[A] Ω[A⁄Λ] :=
  by
    let h' : Function.Surjective (Algebra.ofId A k) := by
      intro y
      rcases h y with ⟨x, hx⟩
      exact ⟨x, hx⟩
    let P := Extension.ofSurjective (Algebra.ofId A k) h'
    change P.Cotangent →ₗ[k] k ⊗[A] Ω[A⁄Λ]
    let l : P.Cotangent →ₗ[A] k ⊗[A] Ω[A⁄Λ] :=
      kerCotangentToTensor Λ A k ∘ₗ P.cotangentEquivCotangentKer.toLinearMap
    exact LinearMap.extendScalarsOfSurjective h' l

/-- The scalar-extended conormal map agrees with the kernel-cotangent
differential under the canonical identification. -/
theorem kerCotangentToTensor_extend_apply (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra A k]
    (h : Function.Surjective (algebraMap A k))
    (x : (Extension.ofSurjective (Algebra.ofId A k) h).Cotangent) :
    kerCotangentToTensor_extend Λ A k h x =
      kerCotangentToTensor Λ A k (Cotangent.val x) := sorry

/-- The extended conormal sequence is exact at the kernel cotangent. -/
theorem exact_toKerCotangent_kerCotangentToTensor_extend
    (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra Λ k] [Algebra A k] [IsScalarTower Λ A k]
    (h : Function.Surjective (algebraMap A k)) :
    Function.Exact (Algebra.H1Cotangent.toKerCotangent Λ A k h)
      (kerCotangentToTensor_extend Λ A k h) := sorry

/-- The extended conormal sequence is exact at the tensor product of
Kähler differentials with the target algebra. -/
theorem exact_kerCotangentToTensor_extend_mapBaseChange
    (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra Λ k] [Algebra A k] [IsScalarTower Λ A k]
    (h : Function.Surjective (algebraMap A k)) :
    Function.Exact (kerCotangentToTensor_extend Λ A k h) (mapBaseChange Λ A k) := sorry

/-- Tensor-extended base change intertwines the conormal maps of
compatible surjections onto a common algebra. -/
@[stacks 06S8]
theorem kerCotangentToTensor_naturality (Λ : Type u) (B : Type v) (A : Type w) (k : Type x)
    [CommRing Λ] [CommRing B] [CommRing A] [CommRing k]
    [Algebra Λ B] [Algebra Λ A] [Algebra Λ k]
    [Algebra B A] [Algebra B k] [Algebra A k]
    [IsScalarTower Λ B A] [IsScalarTower Λ B k] [IsScalarTower Λ A k] [IsScalarTower B A k]
    (hB : Function.Surjective (algebraMap B k))
    (hA : Function.Surjective (algebraMap A k)) :
    tensorMapBaseChange Λ B A k ∘ₗ kerCotangentToTensor_extend Λ B k hB =
      kerCotangentToTensor_extend Λ A k hA ∘ₗ
        Algebra.H1Cotangent.kerCotangentMap B A k hB hA := sorry

end KaehlerDifferential
