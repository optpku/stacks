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

/- Lemma 51.4.4: the cohomological dimension of the sum of two finitely generated ideals
is bounded by the maximum of `-1` and the sum of their cohomological dimensions.
This corrects Tag 0ECP's empty-support boundary: for two unit ideals the printed
ordinary additive bound would read `-1 ≤ -2`. The original additive formula is
available below under its necessary and sufficient numerical condition. -/
@[stacks 0ECP] #check (Ideal.LocalCohomology.dimension_sup_le :
  ∀ {A : Type u} [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG),
    Ideal.LocalCohomology.dimension (I ⊔ J) (Submodule.FG.sup hI hJ) ≤
      max (-1) (Ideal.LocalCohomology.dimension I hI + Ideal.LocalCohomology.dimension J hJ))

#check (Ideal.LocalCohomology.dimension_sup_le_add :
  ∀ {A : Type u} [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG),
    -1 ≤ Ideal.LocalCohomology.dimension I hI + Ideal.LocalCohomology.dimension J hJ →
    Ideal.LocalCohomology.dimension (I ⊔ J) (Submodule.FG.sup hI hJ) ≤
      Ideal.LocalCohomology.dimension I hI + Ideal.LocalCohomology.dimension J hJ)

#check (Ideal.LocalCohomology.dimension_sup_le_add_iff :
  ∀ {A : Type u} [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG),
    (Ideal.LocalCohomology.dimension (I ⊔ J) (Submodule.FG.sup hI hJ) ≤
      Ideal.LocalCohomology.dimension I hI + Ideal.LocalCohomology.dimension J hJ) ↔
    -1 ≤ Ideal.LocalCohomology.dimension I hI + Ideal.LocalCohomology.dimension J hJ)
