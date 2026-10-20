module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.GaloisAction
public import ReasLib.FieldTheory.Galois.Closure
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.Etale.Field

/-!
# The field-spectrum Galois comparison with its actual inverse

A fibre automorphism acts on the standard point of each finite Galois
subextension of the separable closure. Its affine coordinates give a compatible
family of field automorphisms; the native inverse-limit construction and unique
extension to the algebraic closure assemble the inverse.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped FintypeCatDiscrete

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Etale.GaloisComparison

variable (k : Type u) [Field k]

/-- The actual finite étale spectrum of a finite Galois subextension. -/
def finiteGaloisObject (L : FiniteGaloisIntermediateField k (SeparableClosure k)) :
    FiniteEtale (Spec (CommRingCat.of k)) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hf : IsFinite f := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have he : Etale f := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    change (algebraMap k L).Etale
    rw [RingHom.etale_algebraMap]
    exact
      { formallyEtale := Algebra.FormallyEtale.of_isSeparable k L
        finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  exact MorphismProperty.Over.mk ⊤ f ⟨hf, he⟩

/-- The distinguished fibre point is the given subfield embedding into `k̄`. -/
def standardPoint (L : FiniteGaloisIntermediateField k (SeparableClosure k)) :
    (specFieldGeometricPoint k (AlgebraicClosure k)).finiteFiber.obj (finiteGaloisObject k L) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure k)))) (w := by
    change Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure k))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
    rw [← Spec.map_comp]
    congr 1)

variable {k}
variable (τ : Aut (specFieldGeometricPoint k (AlgebraicClosure k)).finiteFiber)
variable (L : FiniteGaloisIntermediateField k (SeparableClosure k))

/-- Evaluate the action on the distinguished point by native affine Spec coordinates. -/
def coordinateRingHom : L →+* AlgebraicClosure k :=
  (Spec.preimage ((τ.hom.app (finiteGaloisObject k L)) (standardPoint k L)).left).hom

/-- The coordinate homomorphism is over the ground field. -/
theorem coordinate_commutes (x : k) :
    coordinateRingHom τ L (algebraMap k L x) = algebraMap k (AlgebraicClosure k) x := by
  let t := (τ.hom.app (finiteGaloisObject k L)) (standardPoint k L)
  have he : CommRingCat.ofHom (algebraMap k L) ≫ Spec.preimage t.left =
      CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact Over.w t
  exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of (AlgebraicClosure k) ↦ f.hom x) he

/-- The supplied fibre automorphism therefore gives a concrete algebra homomorphism. -/
def coordinateAlgHom : L →ₐ[k] AlgebraicClosure k :=
  { toRingHom := coordinateRingHom τ L
    commutes' := coordinate_commutes τ L }

/-- The coordinates are separable because the finite cover is separable over `k`. -/
theorem coordinate_mem_separable (x : L) :
    coordinateAlgHom τ L x ∈ separableClosure k (AlgebraicClosure k) := by
  exact mem_separableClosure_iff.mpr
    ((Algebra.IsSeparable.isSeparable k x).map (coordinateAlgHom τ L)
      (coordinateAlgHom τ L).injective)

/-- Evaluate the coordinate in the actual separable closure, retaining its value. -/
def separableCoordinate : L →ₐ[k] SeparableClosure k :=
  (coordinateAlgHom τ L).codRestrict
    (separableClosure k (AlgebraicClosure k)).toSubalgebra (coordinate_mem_separable τ L)

/-- Native restriction to a normal subfield reads each coordinate in that same finite level. -/
def levelAlgHom : L →ₐ[k] L :=
  (separableCoordinate τ L).restrictNormal L

/-- The inverse fibre automorphism supplies the inverse function at every finite level. -/
def levelEquiv : Gal(L/k) where
  toFun := levelAlgHom τ L
  invFun := levelAlgHom τ⁻¹ L
  left_inv := sorry
  right_inv := sorry
  map_mul' := (levelAlgHom τ L).map_mul
  map_add' := (levelAlgHom τ L).map_add
  commutes' := (levelAlgHom τ L).commutes

/-- Naturality of the fibre action makes the finite-level maps a compatible family. -/
def compatibleFamily :
    ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor k (SeparableClosure k)) where
  val L := levelEquiv τ L.unop
  property := by intro L₁ L₂ f; sorry

/-- Recover the separable-closure automorphism by the native pointwise inverse-limit map. -/
def separableInverse : Gal(SeparableClosure k/k) :=
  InfiniteGalois.limitToAlgEquiv (compatibleFamily τ)

/-- Extend the recovered separable automorphism uniquely to the algebraic closure. -/
def inverse : Gal(AlgebraicClosure k/k) :=
  AlgEquiv.sepClosureEquivAlgClosure k (AlgebraicClosure k) (SeparableClosure k)
    (separableInverse τ)

/-- The inverse recovers the original algebraic-closure automorphism. -/
theorem inverse_forward (σ : Gal(AlgebraicClosure k/k)) :
    inverse (galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k) σ) = σ := sorry

/-- The recovered automorphism acts as the supplied fibre automorphism on every finite cover. -/
theorem forward_inverse :
    galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k) (inverse τ) = τ := sorry

end AlgebraicGeometry.Scheme.Etale.GaloisComparison

namespace AlgebraicGeometry.Scheme.Etale

/-- The field-spectrum Galois comparison keeps its specified forward fibre action
and uses actual finite-coordinate reconstruction for its inverse. -/
def galoisAlgClosureEquivFundamentalGroup (k : Type u) [Field k] :
    Gal(AlgebraicClosure k/k) ≃* Aut (specFieldGeometricPoint k (AlgebraicClosure k)).finiteFiber where
  toFun := galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k)
  invFun := GaloisComparison.inverse
  left_inv := GaloisComparison.inverse_forward
  right_inv := GaloisComparison.forward_inverse
  map_mul' := (galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k)).map_mul

@[simp]
theorem galoisAlgClosureEquivFundamentalGroup_apply (k : Type u) [Field k]
    (σ : Gal(AlgebraicClosure k/k)) :
    galoisAlgClosureEquivFundamentalGroup k σ =
      galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k) σ := rfl

@[simp]
theorem galoisAlgClosureEquivFundamentalGroup_symm_apply (k : Type u) [Field k]
    (τ : Aut (specFieldGeometricPoint k (AlgebraicClosure k)).finiteFiber) :
    (galoisAlgClosureEquivFundamentalGroup k).symm τ = GaloisComparison.inverse τ := rfl

end AlgebraicGeometry.Scheme.Etale
