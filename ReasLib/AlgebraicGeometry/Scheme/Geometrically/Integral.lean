/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Irreducible
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import ReasLib.RingTheory.Algebra.TensorProduct.Reduced

/-!
# Geometrically Integral Affine Schemes Over a Field

This leaf bridges the morphism-level `GeometricallyIntegral` and
`GeometricallyIrreducible` predicates with the ring-level
`Algebra.IsGeometricallyReduced` predicate for an affine scheme over a field.
The mixed presentation is intentional: geometric irreducibility is already
owned by the scheme API, while geometric reducedness has a useful affine ring
criterion.
-/

@[expose] public section

open AlgebraicGeometry CommRingCat
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

namespace GeometricallyIntegral

/-- An affine `k`-scheme is geometrically integral exactly when it is geometrically irreducible
and its coordinate algebra is geometrically reduced over `k`. -/
@[stacks 05DY]
theorem spec_iff :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap k S))) ↔
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))) ∧
        Algebra.IsGeometricallyReduced k S := sorry

end GeometricallyIntegral

section

variable {R : Type u} [CommRing R] [Algebra k R]

/-- Tensoring an integral-domain `k`-algebra with a geometrically integral affine `k`-algebra
produces an integral domain. -/
@[stacks 09P9]
theorem isDomain_tensorProduct_of_geometricallyIntegral_right
    (hS : GeometricallyIntegral (Spec.map (ofHom (algebraMap k S)))) [IsDomain R] :
    IsDomain (R ⊗[k] S) := sorry

end

end AlgebraicGeometry.SchemeOverField
