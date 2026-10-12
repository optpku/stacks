/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap103.Lemma_103_10_8_Hom
import StacksCheckRecall

/-!
# Lemma 103.10.8

On an algebraic stack, sheaf Hom from a finitely presented `𝒪_X`-module into a
quasi-coherent module agrees in `Mod(X_étale, 𝒪_X)` and `Mod(𝒪_X)`, lies in
`LQCoh^{fbc}(𝒪_X)`, and its image under `Q` represents `Hom(H ⊗ F, G)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable (F : fppfModules X) (G H : QCoh X) [F.IsFinitePresentation]

/- Lemma 103.10.8 (1): the internal homs `SheafHom_{𝒪_X}(F, G)` computed in
`Mod(X_étale, 𝒪_X)` and in `Mod(𝒪_X)` agree. -/
@[stacks 0GQN]
#check moduleSheafHom_restrictionIso F G.obj

/- Lemma 103.10.8 (2): the common value is an object of `LQCoh^{fbc}(𝒪_X)`. -/
@[stacks 0GQN]
#check moduleSheafHomLQCohFbc F G

/- Lemma 103.10.8 (3): the quasi-coherent module
`hom(F, G) = Q(SheafHom_{𝒪_X}(F, G))`. -/
@[stacks 0GQN]
#check QCoh.internalHomFP F G

/- Lemma 103.10.8 (4): `Hom_X(H, hom(F, G)) = Hom_X(H ⊗_{𝒪_X} F, G)` for
`H` in `QCoh(𝒪_X)`. -/
@[stacks 0GQN]
#check QCoh.internalHomFP_homEquiv
