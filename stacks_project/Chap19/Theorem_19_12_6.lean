/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.FunctorialResolution
import StacksCheckRecall

@[expose] public section

/-!
# Functorial K-Injective Resolutions

The reusable data, specifications, and existence theorem are owned by ReasLib. This source file
records Theorem 19.12.6 as a typed check of that bundled API.
-/

open CategoryTheory

universe w v u

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/- Theorem 19.12.6: every Grothendieck abelian category admits functorial K-injective
resolutions with termwise injective targets. -/
@[stacks 079P] #check
  (KInjectiveResolution.Functorial.nonempty (C := C) :
    Nonempty (KInjectiveResolution.Functorial C))

/- The source-facing existential view is also reusable without importing this chapter. -/
#check @KInjectiveResolution.Functorial.exists_approximation

end CochainComplex
