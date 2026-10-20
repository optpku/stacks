module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.BaseChange
import StacksCheckRecall

/-!
# Lemma 84.8.5

In the topos square of Lemma 84.8.4, a proper morphism of algebraic spaces
identifies `a_Y⁻¹ ∘ f_small,*` with `f_big,ph,* ∘ a_X⁻¹` on sheaves of sets, and
identifies `a_Y⁻¹(R f_small,* K)` with `R f_big,ph,* (a_X⁻¹ K)` for `K` in
`D⁺(X_étale)` with torsion cohomology sheaves. Here `a_X = π_X ∘ ε_X` and
`a_Y = π_Y ∘ ε_Y`.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PhComparison
open CategoryTheory

universe u

/- Lemma 84.8.5 (1): proper direct image commutes with inverse image from the
small étale topos to the big ph topos on sheaves of sets. -/
@[stacks 0DGX] #check
  (AlgebraicGeometry.AlgebraicSpace.PhComparison.proper_smallPhPushforward_isIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f],
      IsIso (smallPhPushforwardHom f))

/- Lemma 84.8.5 (2): the canonical bounded-below derived comparison is invertible
for complexes with torsion cohomology sheaves. -/
@[stacks 0DGX] #check
  (AlgebraicGeometry.AlgebraicSpace.PhComparison.proper_plusSmallPhPushforward_isIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
      (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
      (hK : DerivedCategory.Plus.cohomologyIn
        (Sheaf.torsion (smallEtaleTopology X)) K),
      IsIso ((plusSmallPhPushforwardHom f).app K))
