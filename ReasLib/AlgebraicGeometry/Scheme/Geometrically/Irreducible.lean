/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Geometric Irreducibility of Affine Tensor Products

This leaf presents the affine tensor-product form of base-change stability for
`GeometricallyIrreducible`.  The named theorem is available for explicit
transport, while the corresponding instance lets typeclass search use the
canonical base-change fact without rebuilding the pullback comparison.
-/

@[expose] public section

open AlgebraicGeometry CommRingCat CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k R S : Type u}
variable [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- Geometric irreducibility of an affine `k`-algebra is preserved by tensoring with an
arbitrary affine `k`-algebra. -/
@[stacks 037O]
theorem geometricallyIrreducible_tensorProduct_projection
    (hS : GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S)))) :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap R (R ⊗[k] S)))) := sorry

/-- The tensor-product projection of a geometrically irreducible affine `k`-scheme is
geometrically irreducible. -/
@[stacks 037O "tensor-product base-change instance"]
instance instGeometricallyIrreducible_tensorProduct_projection
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S)))] :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap R (R ⊗[k] S)))) :=
  geometricallyIrreducible_tensorProduct_projection inferInstance

/-- The tensor-product projection induces an equivalence on irreducible components when the
right affine factor is geometrically irreducible over `k`. -/
@[stacks 037O]
noncomputable def irreducibleComponentsEquiv_tensorProduct_projection
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S)))]
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap R (R ⊗[k] S))))] :
    irreducibleComponents (Spec (of (R ⊗[k] S))) ≃
      irreducibleComponents (Spec (of R)) :=
  (Spec.map (ofHom (algebraMap R (R ⊗[k] S)))).irreducibleComponentsEquiv
    (by
      rw [Spec.map_base]
      exact PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field)

end AlgebraicGeometry.SchemeOverField
