/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Discriminant
import StacksCheckRecall

@[expose] public section

universe u v w

/- Definition 9.20.8 (Tag 0BIM): the discriminant of a finite field extension `L/K` is the
square class of the discriminant of its trace pairing. The reusable owner is
`FieldExtension.discriminant`; its basis-independent computation rule is
`FieldExtension.discriminant_eq`. -/

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

@[stacks 0BIM]
#check (FieldExtension.discriminant K L : FieldExtension.SquareClassWithZero K)
#check (FieldExtension.discriminant_eq (K := K) (L := L) :
  (b : Module.Basis ι K L) →
    FieldExtension.discriminant K L =
      FieldExtension.SquareClassWithZero.mk K (Algebra.discr K b))
