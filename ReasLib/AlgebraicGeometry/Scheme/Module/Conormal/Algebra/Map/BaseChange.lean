/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Algebra.Map.Affine
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Tensor

/-!
# Base change for conormal algebras

The canonical map of conormal algebras associated to a cartesian square of scheme immersions
is degreewise an epimorphism and is an isomorphism under flat base change.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ConormalAlgebra

variable {Z X Z' X' : Scheme.{u}}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
variable [IsImmersion i] [IsImmersion i']

/-- Every homogeneous component of the canonical conormal-algebra comparison associated to a
cartesian square of scheme immersions is an epimorphism. -/
theorem map_component_epi_of_isPullback (sq : IsPullback f i i' g) (n : ℕ) :
    Epi ((map sq.toCommSq).hom n) := sorry

/-- The canonical conormal-algebra comparison associated to a cartesian square of scheme
immersions is an isomorphism when the ambient morphism is flat. -/
theorem map_isIso_of_isPullback_of_flat [Flat g] (sq : IsPullback f i i' g) :
    IsIso (C := SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} Z.sheaf ℕ)
      (map sq.toCommSq) := sorry

end AlgebraicGeometry.Scheme.ConormalAlgebra
