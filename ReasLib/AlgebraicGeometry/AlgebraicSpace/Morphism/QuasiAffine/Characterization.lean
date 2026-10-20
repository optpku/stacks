/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Factorization

/-!
# Quasi-affine morphisms via relative spectrum factorization

A qcqs morphism of algebraic spaces is quasi-affine iff the canonical first factor
through the relative spectrum of the pushforward structure sheaf is an open
immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace QuasiAffine

/-- A qcqs morphism of algebraic spaces is quasi-affine iff the canonical morphism
to the relative spectrum of the pushforward structure sheaf is an open immersion. -/
theorem iff_isOpenImmersion_toPushforwardRelativeSpec {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    QuasiAffine f ↔ IsOpenImmersion (Hom.toPushforwardRelativeSpec f) :=
  sorry

/-- A qcqs morphism of algebraic spaces whose canonical morphism to the relative
spectrum of the pushforward structure sheaf is an open immersion is quasi-affine. -/
theorem of_isOpenImmersion_toPushforwardRelativeSpec {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsOpenImmersion (Hom.toPushforwardRelativeSpec f)] : QuasiAffine f :=
  (iff_isOpenImmersion_toPushforwardRelativeSpec f).mpr inferInstance

end QuasiAffine

/-- The canonical morphism of a qcqs quasi-affine morphism of algebraic spaces into
the relative spectrum of the pushforward structure sheaf is an open immersion. -/
theorem instIsOpenImmersion_toPushforwardRelativeSpec {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [QuasiAffine f] : IsOpenImmersion (Hom.toPushforwardRelativeSpec f) :=
  (QuasiAffine.iff_isOpenImmersion_toPushforwardRelativeSpec f).mp inferInstance

end AlgebraicGeometry.AlgebraicSpace
