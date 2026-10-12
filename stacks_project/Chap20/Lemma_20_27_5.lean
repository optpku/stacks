/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Tensor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open scoped RingedSpaceDerivedPullback RingedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}
variable (f : X ⟶ Y)

/-
Lemma 20.27.5 (0FP0): for literal complexes `K` and `M`, the pullback--tensor comparison from
Lemma 20.27.3 can be chosen compatibly with the canonical derived-functor counits.  This is the
cochain-representative specialization of the reusable comparison square.
-/

variable (K M : CochainComplex (Modules Y) ℤ)

@[stacks 0FP0 "Lemma 20.27.5: pullback--tensor comparison on cochain representatives"]
#check ModuleDerived.Pullback.existsTensorIso_commSq f
  ((HomotopyCategory.quotient (Modules Y) (up ℤ)).obj K) (DerivedCategory.Q.obj M)

#check @ModuleDerived.Pullback.existsTensorIso_commSq
#check @ModuleDerived.Pullback.sourceCounit
#check @ModuleDerived.Pullback.targetCounit

end AlgebraicGeometry.RingedSpace

end
