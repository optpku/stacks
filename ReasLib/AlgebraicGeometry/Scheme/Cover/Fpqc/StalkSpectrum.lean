/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Stalk.Coproduct
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace

/-!
# The affine-line stalk-spectrum morphism

The coproduct of the spectra of all stalks of the affine line is flat and
surjective over the affine line, but is not quasi-compact or an fpqc singleton
covering.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Fpqc.AffineLineStalkSpectrum

/-- The stalk-spectrum coproduct morphism for the affine line over a field is
flat. -/
theorem flat (k : Type u) [Field k] :
    Flat (AlgebraicGeometry.stalkSpectrumCoproductTo
      (PuncturedAffineSpace.coordinateSpectrum (Fin 1) k)) := sorry

/-- The stalk-spectrum coproduct morphism for the affine line over a field is
surjective. -/
theorem surjective (k : Type u) [Field k] :
    Surjective (AlgebraicGeometry.stalkSpectrumCoproductTo
      (PuncturedAffineSpace.coordinateSpectrum (Fin 1) k)) := sorry

/-- The stalk-spectrum coproduct morphism for the affine line over a field is
not quasi-compact. -/
theorem not_quasiCompact (k : Type u) [Field k] :
    ¬ QuasiCompact (AlgebraicGeometry.stalkSpectrumCoproductTo
      (PuncturedAffineSpace.coordinateSpectrum (Fin 1) k)) := sorry

/-- The singleton family of the affine-line stalk-spectrum coproduct morphism
is not fpqc-covering. -/
theorem not_covering (k : Type u) [Field k] :
    ¬ Scheme.FpqcCovering
      (fun _ : PUnit ↦ CategoryTheory.Over.mk
        (AlgebraicGeometry.stalkSpectrumCoproductTo
          (PuncturedAffineSpace.coordinateSpectrum (Fin 1) k))) := sorry

end AlgebraicGeometry.Scheme.Fpqc.AffineLineStalkSpectrum
