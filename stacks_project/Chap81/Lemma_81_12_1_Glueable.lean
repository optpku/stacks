/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.BeauvilleLaszlo

/-!
# Glueable global sections over Spec R

A scheme over `Spec R` has glueable global sections for `(R → R', f)` when the
Beauville-Laszlo module Cech sequence of `Γ(T.left, ⊤)` is short exact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

#check (Scheme.Hom.glueableGlobalSections :
  {R : Type u} → [CommRing R] →
    (R' : Type u) → [CommRing R'] → [Algebra R R'] →
    (f : R) → (T : Over (Spec (CommRingCat.of R))) → Prop)

#check (Scheme.Hom.glueableGlobalSections_iff :
  {R : Type u} → [CommRing R] →
    (R' : Type u) → [CommRing R'] → [Algebra R R'] →
    (f : R) → (T : Over (Spec (CommRingCat.of R))) →
      (Scheme.Hom.glueableGlobalSections R' f T ↔
        (beauvilleLaszloModuleCechSequence R'
          (Scheme.Hom.globalSectionsAlg T.hom) f).ShortExact))
