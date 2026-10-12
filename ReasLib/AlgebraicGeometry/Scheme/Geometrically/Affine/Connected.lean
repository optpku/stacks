/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Adjoin.FGBaseChange
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Group.Idempotent.Map
public import ReasLib.Algebra.Category.CommAlgCat.FilteredColimit
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.FiniteSeparable
public import ReasLib.Topology.ConnectedComponents.Maps

/-!
# Closure of Affine Geometric Connectedness

This leaf owns closure of mathlib's canonical `GeometricallyConnected`
predicate for affine algebras over a field.  It is deliberately parallel to
the irreducible leaf while keeping the two distinct obstruction arguments out
of the public API.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits CommRingCat
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry.SchemeOverField

namespace GeometricallyConnected

section

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- Geometric connectedness descends along an injective morphism of affine algebras over a
field. -/
@[stacks 037V "injective affine descent"]
theorem of_injective
    {B : Type u} [CommRing B] [Algebra k B]
    (f : B →ₐ[k] A) (hf : Function.Injective f)
    (hA : GeometricallyConnected (Spec.map (ofHom (algebraMap k A)))) :
    GeometricallyConnected (Spec.map (ofHom (algebraMap k B))) := sorry

/-- Lemma 10.48.5 (1) (Tag 037V): every subalgebra of a geometrically connected affine
algebra over a field is geometrically connected. -/
@[stacks 037V]
theorem of_subalgebra
    (S : Subalgebra k A)
    (hA : GeometricallyConnected (Spec.map (ofHom (algebraMap k A)))) :
    GeometricallyConnected (Spec.map (ofHom (algebraMap k S))) := sorry

/-- A subalgebra of a geometrically connected affine algebra inherits the canonical
geometric-connectedness instance. -/
@[stacks 037V "subalgebra instance"]
instance instSubalgebra
    (S : Subalgebra k A)
    [GeometricallyConnected (Spec.map (ofHom (algebraMap k A)))] :
    GeometricallyConnected (Spec.map (ofHom (algebraMap k S))) := sorry

/-- Lemma 10.48.5 (2) (Tag 037V): geometric connectedness of every finitely generated
subalgebra implies geometric connectedness of the ambient affine algebra. -/
@[stacks 037V]
theorem of_forall_fg
    (h : ∀ S : Subalgebra k A, S.FG →
      GeometricallyConnected (Spec.map (ofHom (algebraMap k S)))) :
    GeometricallyConnected (Spec.map (ofHom (algebraMap k A))) := sorry

end

section

variable {k : Type u} {I : Type v} [Field k]
variable [Category I] [IsFilteredOrEmpty I]

/-- Lemma 10.48.5 (3) (Tag 037V): a filtered-or-empty colimit of geometrically connected
affine algebras over a field is geometrically connected. -/
@[stacks 037V]
theorem of_filteredColimit
    (F : I ⥤ CommAlgCat.{u} k) [HasColimit F]
    (hF : ∀ i, GeometricallyConnected
      (Spec.map (ofHom (algebraMap k (F.obj i))))) :
    GeometricallyConnected
      (Spec.map (ofHom (algebraMap k (colimit F : CommAlgCat.{u} k)))) := sorry

end

end GeometricallyConnected

namespace GeometricallyConnected.Spectrum

section

variable {k S : Type u}
variable [Field k] [CommRing S] [Algebra k S]

/-- Lemma 10.48.4 (Tag 037U): over a separably closed field, geometric connectedness of an
affine algebra is equivalent to connectedness of its prime spectrum. -/
@[stacks 037U]
theorem iff_connectedSpace_of_isSepClosed [IsSepClosed k] :
    GeometricallyConnected (Spec.map (ofHom (algebraMap k S))) ↔
      ConnectedSpace (PrimeSpectrum S) := sorry

/-- Lemma 10.48.2 (Tag 037S): an affine algebra over a field is geometrically
connected exactly when its prime spectrum stays connected after every finite
separable field extension. -/
@[stacks 037S]
theorem iff_finiteSeparable :
    GeometricallyConnected (Spec.map (ofHom (algebraMap k S))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
        [Algebra.IsSeparable k K],
        ConnectedSpace (PrimeSpectrum (S ⊗[k] K)) := sorry

end

end GeometricallyConnected.Spectrum

namespace GeometricallyConnected.TensorProduct

section

variable {k R S : Type u}
variable [Field k] [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]

/-- Lemma 10.48.6 (Tag 037W), idempotent clause: if `S` is geometrically connected over `k`,
the tensor-product inclusion induces a bijection on idempotent elements. -/
@[stacks 037W]
theorem idempotentMap_bijective
    (hS : GeometricallyConnected (Spec.map (ofHom (algebraMap k S)))) :
    Function.Bijective
      (((Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S).toRingHom).idempotentMap) := sorry

/-- Lemma 10.48.6 (Tag 037W), connected-components clause: if `S` is geometrically connected
over `k`, the tensor-product projection induces a bijection on connected components. -/
@[stacks 037W]
theorem connectedComponentsMap_bijective
    (hS : GeometricallyConnected (Spec.map (ofHom (algebraMap k S)))) :
    Function.Bijective
      ((PrimeSpectrum.continuous_comap
        (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S)).connectedComponentsMap :
        ConnectedComponents (PrimeSpectrum (R ⊗[k] S)) →
          ConnectedComponents (PrimeSpectrum R)) := sorry

/-- A geometrically connected tensor factor preserves connectedness of the prime spectrum of a
connected affine algebra. -/
@[stacks 037W "connected tensor-product consequence"]
theorem connectedSpace_of_connected
    (hR : ConnectedSpace (PrimeSpectrum R))
    (hS : GeometricallyConnected (Spec.map (ofHom (algebraMap k S)))) :
    ConnectedSpace (PrimeSpectrum (R ⊗[k] S)) := sorry

/-- Lemma 10.48.1 (Tag 037R): over a separably closed field, the tensor product
of two affine algebras with connected prime spectra has connected prime spectrum. -/
@[stacks 037R]
theorem connectedSpace_of_isSepClosed [IsSepClosed k]
    (hR : ConnectedSpace (PrimeSpectrum R))
    (hS : ConnectedSpace (PrimeSpectrum S)) :
    ConnectedSpace (PrimeSpectrum (R ⊗[k] S)) := sorry

end

end GeometricallyConnected.TensorProduct

end AlgebraicGeometry.SchemeOverField
