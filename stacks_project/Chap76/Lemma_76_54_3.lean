module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Thickening.PseudoCoherent
import StacksCheckRecall

/-!
# Pseudo-coherence along finite-order thickenings of algebraic spaces

If `i : X ⟶ X'` is a finite-order thickening of algebraic spaces over a scheme
and `K'` is an object of `D(𝒪_{X'})` whose derived pullback `Li^* K'` is
pseudo-coherent, then `K'` itself is pseudo-coherent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.54.3: Let `S` be a scheme. Let `i : X ⟶ X'` be a finite-order
thickening of algebraic spaces. Let `K'` in `D(𝒪_{X'})` be an object such that
`K = Li^* K'` is pseudo-coherent, where `Li^*` is `modulePullbackDerived i`.
Then `K'` is pseudo-coherent. -/
@[stacks 0DL3]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.isPseudoCoherent_of_pullback :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFiniteOrderThickening i] (K' : ModuleDerived X'),
    IsPseudoCoherent X ((modulePullbackDerived i).obj K') → IsPseudoCoherent X' K')
