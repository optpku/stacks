/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocal

/-!
# Gorenstein algebraic spaces

Gorensteinness can be tested on a surjective étale scheme atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is Gorenstein if it admits a representable étale
locally-surjective atlas from a Gorenstein scheme. -/
@[mk_iff]
class IsGorenstein {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- There is a representable étale locally-surjective atlas from a Gorenstein
  scheme. -/
  exists_gorenstein_etaleCover :
    existsSurjectiveEtale (Scheme.Gorenstein : ObjectProperty Scheme.{u}) X

namespace IsGorenstein

/-- A Gorenstein algebraic space admits a representable étale locally-surjective
atlas from a Gorenstein scheme. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsGorenstein X] :
    existsSurjectiveEtale (Scheme.Gorenstein : ObjectProperty Scheme.{u}) X :=
  IsGorenstein.exists_gorenstein_etaleCover

/-- A representable étale locally-surjective atlas from a Gorenstein scheme
witnesses that the algebraic space is Gorenstein. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsSurjectiveEtale (Scheme.Gorenstein : ObjectProperty Scheme.{u}) X) :
    IsGorenstein X :=
  ⟨h⟩

end IsGorenstein

/-- A Gorenstein scheme over `S`, viewed as an algebraic space, is Gorenstein. -/
instance instIsGorenstein_ofOver {S : Scheme.{u}} (T : Over S)
    [Scheme.Gorenstein T.left] : IsGorenstein (ofOver T) where
  exists_gorenstein_etaleCover :=
    (existsSurjectiveEtale_ofOver (Scheme.Gorenstein : ObjectProperty Scheme.{u}) T).mpr
      inferInstance

/-- An algebraic space is Gorenstein if and only if every étale morphism from a
scheme to it has Gorenstein source. -/
theorem isGorenstein_iff_forallEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsGorenstein X ↔
      forallEtale (Scheme.Gorenstein : ObjectProperty Scheme.{u}) X :=
  ⟨fun h ↦ (existsSurjectiveEtale_iff_forallEtale _ X).mp h.exists_gorenstein_etaleCover,
    fun h ↦ ⟨(existsSurjectiveEtale_iff_forallEtale _ X).mpr h⟩⟩

end AlgebraicGeometry.AlgebraicSpace
