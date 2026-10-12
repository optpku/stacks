/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.DirectedSystem
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (rings : I → CommRingCat.{v})
variable (transition : ∀ {i j : I}, i ≤ j → (rings i ⟶ rings j))
variable (compatibility : CommRingCat.IsCompatibleSystem rings transition)

/- Definition 111.2.3: the ring constructed in Exercise 111.2.2 is called the colimit of the
system, denoted `colim A_i`. Its underlying ring is
`Ring.DirectLimit (fun i => rings i) (fun _ _ inequality => transition inequality)`. -/
@[stacks 078K]
#check (CommRingCat.directLimit rings transition compatibility : CommRingCat.{max u v})
