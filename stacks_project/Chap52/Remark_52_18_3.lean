module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Distance.Properties

universe u

open Set TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry AlgebraicGeometry.Scheme

/- Remark 52.18.3: the pointwise bound below expresses the displayed inequality by
bounding `Y.distanceTo Z` by every admissible specialization-pattern length. The claimed
finite-type equality and compatibility of the alternative definition with Lemma 52.18.2
are deliberately left unformalized in the source. -/
@[stacks 0EJ0] #check (AlgebraicGeometry.Scheme.distanceTo_le_of_specialization_pattern :
    ∀ {Y : AlgebraicGeometry.Scheme.{u}} [IsNoetherian Y] [CatenarySpace Y]
      (Z : Closeds Y) (k : ℕ) (y : Fin (k + 1) → Y) (y' : Fin k → Y)
      (hy0 : y 0 ∈ Z)
      (hleft : ∀ i : Fin k, IsImmediateSpecialization (y' i) (y i.castSucc))
      (hright : ∀ i : Fin k, y' i ⤳ y i.succ),
      Y.distanceTo Z (y (Fin.last k)) ≤ k)
