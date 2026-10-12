/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.InverseSystem.TensorProduct.Derived.Interleaving
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u x v w

namespace DifferentialGradedModule.InverseSystem

variable {R : Type u} [CommRing R]
variable {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
variable {N N' : LeftSystem.{u, x, w} A}
variable (hNN' : LeftSystem.Derived.AreProIsomorphic N N')
variable (M : Derived.Category.{u, x, v} A)
variable {K K' : DerivedCategory (ModuleCat.{max v w} R)}
variable (hK : IsDerivedLimit (TensorProduct.Derived.RepresentedLeft.tower M N) K)
variable (hK' : IsDerivedLimit (TensorProduct.Derived.RepresentedLeft.tower M N') K')

/- Lemma 24.35.2 (tag 0GZI): derived pro-isomorphic ordinary left DG-module systems have
noncanonically isomorphic chosen derived limits after stagewise relative derived tensor with
every object of `D(ℕ, A)`. -/
@[stacks 0GZI "derived-limit invariance for derived pro-isomorphic left systems"]
#check
  (hNN'.nonemptyIso_tensorDerivedLimit M hK hK' : Nonempty (K ≅ K'))

end DifferentialGradedModule.InverseSystem
