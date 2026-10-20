/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.RingTheory.Gorenstein.Regular
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 47.21.3 (1): A regular local ring is Gorenstein. -/
@[stacks 0AWX] #check (IsRegularLocalRing.instIsGorensteinLocalRing :
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R], IsGorensteinLocalRing R)

/- Lemma 47.21.3 (2): A regular ring is Gorenstein. -/
@[stacks 0AWX] #check (IsRegularRing.instIsGorensteinRing :
  ∀ (R : Type u) [CommRing R] [IsRegularRing R], IsGorensteinRing R)
