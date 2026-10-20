/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 51.4.5 (1): extending a finitely generated ideal along a ring homomorphism
cannot increase its local-cohomological dimension. -/
@[stacks 0DXA] #check (Ideal.LocalCohomology.dimension_map_le :
  ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (hI : I.FG),
    Ideal.LocalCohomology.dimension (I.map f) (hI.map f) ≤
      Ideal.LocalCohomology.dimension I hI)

/- Lemma 51.4.5 (2): faithfully flat extension preserves the
local-cohomological dimension of a finitely generated ideal. -/
@[stacks 0DXA] #check (Ideal.LocalCohomology.dimension_map_eq_of_faithfullyFlat :
  ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A)
    (hI : I.FG) (hf : f.FaithfullyFlat),
    Ideal.LocalCohomology.dimension (I.map f) (hI.map f) =
      Ideal.LocalCohomology.dimension I hI)
