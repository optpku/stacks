/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleCech
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

/-!
# Glueable global sections over an affine base

The structure morphism to `Spec R` supplies the module structure used in the
Beauville-Laszlo module Cech sequence of global sections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Global sections of a scheme over `Spec R` are glueable when their
Beauville-Laszlo module Cech sequence is short exact, using the `R`-module
structure induced by the structure morphism. -/
abbrev glueableGlobalSections {R : Type u} [CommRing R]
    (R' : Type u) [CommRing R'] [Algebra R R'] (f : R)
    (T : Over (Spec (CommRingCat.of R))) : Prop :=
  (beauvilleLaszloModuleCechSequence R' (globalSectionsAlg T.hom) f).ShortExact

/-- Glueability of global sections is equivalent to short exactness of their
Beauville-Laszlo module Cech sequence with the structure-map-induced algebra. -/
theorem glueableGlobalSections_iff {R : Type u} [CommRing R]
    (R' : Type u) [CommRing R'] [Algebra R R'] (f : R)
    (T : Over (Spec (CommRingCat.of R))) :
    glueableGlobalSections R' f T ↔
      (beauvilleLaszloModuleCechSequence R' (globalSectionsAlg T.hom) f).ShortExact :=
  Iff.rfl

end AlgebraicGeometry.Scheme.Hom
