/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Cover
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Pushforward
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Affine morphisms and relative spectra

Affine morphisms are characterized by relative-spectrum models, and the canonical morphism to
the relative spectrum of the pushed-forward structure sheaf is an isomorphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- For an affine morphism, the canonical morphism to any relative-spectrum model of its
pushed-forward structure sheaf is an isomorphism. -/
theorem isIso_pushforwardStructureSheafRelativeSpectrumHom
    (f : X ⟶ S) [IsAffineHom f]
    (P : RelativeSpectrumOver (pushforwardStructureSheafQcAlgebra f))
    [IsRelativeSpectrumOver P] :
    IsIso (pushforwardStructureSheafRelativeSpectrumHom f P) := sorry

/-- A scheme morphism is affine if and only if it is isomorphic over its target to an explicit
relative-spectrum model of a quasi-coherent algebra sheaf. -/
theorem isAffineHom_iff_exists_iso_relativeSpec (f : X ⟶ S) :
    IsAffineHom f ↔
      ∃ (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A),
        IsRelativeSpectrumOver P ∧
          Nonempty (Over.mk f ≅ Over.mk (relativeSpecπ P)) := sorry

end AlgebraicGeometry.Scheme
