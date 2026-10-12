/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Irreducible
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-
Lemma 28.3.3: A scheme is irreducible exactly when it admits a nonempty affine open cover
by irreducible members whose pairwise intersections are nonempty.
-/
@[stacks 01OM] #check
  (AlgebraicGeometry.Scheme.irreducibleSpace_iff_exists_affineOpenCover X :
    IrreducibleSpace X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        Nonempty 𝒰.I₀ ∧
          (∀ i : 𝒰.I₀, IsIrreducible ((𝒰.f i).opensRange : Set X)) ∧
            ∀ i j : 𝒰.I₀,
              (((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange : X.Opens) : Set X).Nonempty)

#check
  (AlgebraicGeometry.Scheme.irreducibleSpace_iff_nonempty_and_forall_nonempty_affineOpen X :
    IrreducibleSpace X ↔
      Nonempty X ∧
        ∀ U : X.affineOpens,
          ((U : Set X).Nonempty → IsIrreducible (U : Set X)))

end AlgebraicGeometry.Scheme
