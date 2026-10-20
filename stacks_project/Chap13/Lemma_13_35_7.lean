module

import ReasLib.CategoryTheory.DerivedCategory.Limit.Extension.Derived
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.35.7

The four interval-generation criteria are owned by the neutral derived-category
extension API. The shared statements do not require a separate hypothesis
`a ≤ b`; hence they also directly imply the source formulations.
-/

/- Lemma 13.35.7 (Stacks 0FX7) (1): cohomology supported on `[a, b]` and
taking values in `E` puts a derived object in the corresponding additive
extension stage. -/
@[stacks 0FX7] #check
  @DerivedCategory.IntervalExtension.mem_of_homology

/- Lemma 13.35.7 (Stacks 0FX7) (2): the same conclusion holds when the
cohomology objects lie in `smd(add(E))`. -/
@[stacks 0FX7] #check
  @DerivedCategory.IntervalExtension.Closure.mem_of_homology

/- Lemma 13.35.7 (Stacks 0FX7) (3): a representative supported on `[a, b]`
whose terms lie in `E` puts its derived object in the corresponding additive
extension stage. -/
@[stacks 0FX7] #check
  @DerivedCategory.IntervalExtension.mem_of_representative

/- Lemma 13.35.7 (Stacks 0FX7) (4): the representative criterion also holds
when its terms lie in `smd(add(E))`. -/
@[stacks 0FX7] #check
  @DerivedCategory.IntervalExtension.Closure.mem_of_representative
