/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.FormalObjectSystem
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving
public import stacks_project.Chap98.Definition_98_13_1_Openness
public import stacks_project.Chap98.Definition_98_18_1
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strong formal effectiveness implies openness of versality

On a locally Noetherian base, a category fibred in groupoids over `(Sch/S)_fppf`
with representable-by-algebraic-spaces diagonal, (RS*), and limit preservation,
and for which Remark 98.20.2 systems with pairwise square-zero kernels are
effective, satisfies openness of versality.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.FormalObjectSystem

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C] {p : C ⥤ Over S}
variable (ξ : FormalObjectSystem p)

/-- Pairwise kernels of transition maps of a formal object system have square
zero: for all `n ≤ m`, `Ker(R_m ⟶ R_n)` squares to zero. -/
def KernelSquareZero : Prop :=
  ∀ {m n : ℕ} (hmn : n ≤ m),
    RingHom.ker (ξ.ringSystem.transitionMap hmn).hom ^ 2 = ⊥

/-- `KernelSquareZero` means every transition map `R_m ⟶ R_n` for `n ≤ m` has
square-zero kernel. -/
theorem kernelSquareZero_iff :
    ξ.KernelSquareZero ↔
      ∀ {m n : ℕ} (hmn : n ≤ m),
        RingHom.ker (ξ.ringSystem.transitionMap hmn).hom ^ 2 = ⊥ :=
  sorry

end AlgebraicGeometry.FormalObjectSystem

namespace AlgebraicGeometry.GroupoidsOver

/-- Lemma 98.20.3: let `S` be a locally Noetherian scheme. Let `X` be a
category fibred in groupoids over `(Sch/S)_fppf`. Assume the diagonal
`Δ : X ⟶ X × X` is representable by algebraic spaces, `X` has (RS*), `X` is
limit preserving, and systems as in Remark 98.20.2 for which
`Ker(R_m ⟶ R_n)` is square zero for all `m ≥ n` are effective. Then `X`
satisfies openness of versality. -/
@[stacks 0CXU]
theorem OpennessOfVersality.of_squareZeroKernelEffectiveness
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] [Groupoids.LimitPreserving X]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (h_eff : ∀ ξ : FormalObjectSystem X.p, ξ.KernelSquareZero → ξ.IsEffective) :
    OpennessOfVersality X :=
  sorry

end AlgebraicGeometry.GroupoidsOver
