/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Smooth.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.137.1

@stack 00T2
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Domain triage:
- primary domain: smooth commutative algebra maps and their cotangent-theoretic consequences;
- sampled owner declarations:
  `Algebra.Smooth`,
  `Algebra.Smooth.finitePresentation`,
  `Algebra.FormallySmooth.subsingleton_h1Cotangent`,
  `KaehlerDifferential.finite`;
- best owner abstraction: `Algebra.Smooth R S`;
- primitive data: the smoothness owner instance on the `R`-algebra `S`;
- derived API: finite presentation of `S`, vanishing of `H¹(L_{S/R})`, and projective/finite
  Kähler differentials.

This file is therefore a `core/canonical` recall file: it should reuse the owner declarations
directly and avoid any parallel local smoothness wrapper.
-/
/- Definition 10.137.1: a ring map `R → S` is smooth when the corresponding `R`-algebra `S` is
smooth, i.e. of finite presentation and with naive cotangent complex quasi-isomorphic to a finite
projective module concentrated in degree `0`. -/
@[stacks 00T2 "smooth algebra predicate"]
#check @Smooth

/- Smooth algebras are finitely presented over the base ring. -/
@[stacks 00T2 "finite presentation"]
#check @Smooth.finitePresentation

/- Smooth `R`-algebras have vanishing first homology of the naive cotangent complex. -/
@[stacks 00T2 "first cotangent homology"]
#check @FormallySmooth.subsingleton_h1Cotangent

/- Smooth `R`-algebras have projective Kähler differentials. -/
@[stacks 00T2 "projective Kahler differentials"]
#check @FormallySmooth.projective_kaehlerDifferential

section

variable [Smooth R S]

/- Smooth `R`-algebras have finite Kähler differentials. -/
@[stacks 00T2 "finite Kahler differentials"]
#check @KaehlerDifferential.finite

end

end Algebra
