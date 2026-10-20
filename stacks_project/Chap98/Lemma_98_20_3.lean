module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpennessOfVersality.StrongEffectiveness
import StacksCheckRecall

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

#check (AlgebraicGeometry.FormalObjectSystem.KernelSquareZero :
  ∀ {S : Scheme.{u}} {C : Type v} [Category.{w} C] {p : C ⥤ Over S},
    FormalObjectSystem p → Prop)

#check (AlgebraicGeometry.FormalObjectSystem.kernelSquareZero_iff :
  ∀ {S : Scheme.{u}} {C : Type v} [Category.{w} C] {p : C ⥤ Over S}
    (ξ : FormalObjectSystem p),
    ξ.KernelSquareZero ↔
      ∀ {m n : ℕ} (hmn : n ≤ m),
        RingHom.ker (ξ.ringSystem.transitionMap hmn).hom ^ 2 = ⊥)

/- Lemma 98.20.3: let `S` be a locally Noetherian scheme. Let `X` be a
category fibred in groupoids over `(Sch/S)_fppf`. Assume the diagonal
`Δ : X ⟶ X × X` is representable by algebraic spaces, `X` has (RS*), `X` is
limit preserving, and systems as in Remark 98.20.2 for which
`Ker(R_m ⟶ R_n)` is square zero for all `m ≥ n` are effective. Then `X`
satisfies openness of versality. -/
@[stacks 0CXU] #check
  (AlgebraicGeometry.GroupoidsOver.OpennessOfVersality.of_squareZeroKernelEffectiveness :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [GroupoidsOver.HasStrongRimSchlessinger X] [Groupoids.LimitPreserving X]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (h_eff : ∀ ξ : FormalObjectSystem X.p, ξ.KernelSquareZero → ξ.IsEffective),
    GroupoidsOver.OpennessOfVersality X)
