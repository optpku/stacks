/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSheaf

/-!
# Structure-sheaf characterization of scheme-theoretic density

An open immersion of algebraic spaces is scheme-theoretically dense if and only
if the direct-image structure-sheaf map is a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsSchemeTheoreticallyDense

/-- An open immersion of algebraic spaces over a scheme is scheme-theoretically
dense if and only if its canonical structure-sheaf map is a monomorphism. -/
theorem iff_mono_structureSheafMap {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] :
    IsSchemeTheoreticallyDense ι ↔ Mono (structureSheafMap ι) :=
  sorry

/-- Injectivity of `𝒪_X ⟶ ι_* 𝒪_U` implies scheme-theoretic density of the open
immersion. -/
theorem of_mono_structureSheafMap {S : Scheme.{u}} {X U : AlgebraicSpace S}
    {ι : U ⟶ X} [IsOpenImmersion ι] (h : Mono (structureSheafMap ι)) :
    IsSchemeTheoreticallyDense ι :=
  (iff_mono_structureSheafMap ι).mpr h

/-- Scheme-theoretic density of an open immersion implies that
`𝒪_X ⟶ ι_* 𝒪_U` is a monomorphism. -/
instance mono_structureSheafMap {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] [IsSchemeTheoreticallyDense ι] :
    Mono (structureSheafMap ι) :=
  (iff_mono_structureSheafMap ι).mp inferInstance

/-- Scheme-theoretic density of an open immersion is equivalent to vanishing of
the kernel ideal sheaf of `𝒪_X ⟶ ι_* 𝒪_U`. -/
theorem iff_idealSheafSubobject_eq_bot {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] :
    IsSchemeTheoreticallyDense ι ↔ Hom.idealSheafSubobject ι = ⊥ :=
  sorry

end IsSchemeTheoreticallyDense

end AlgebraicGeometry.AlgebraicSpace
