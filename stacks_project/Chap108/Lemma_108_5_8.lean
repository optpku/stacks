module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Precomposition

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.5.8: A surjection of quasi-coherent modules on a separated
algebraic space of finite presentation over the base induces the canonical
closed immersion of Grothendieck Quot functors by precomposition. -/
@[stacks 0DP5] #check
  (AlgebraicGeometry.AlgebraicSpace.Quot.isClosedImmersion_precompHom :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [FinitePresentation f] [Separated f] {F G : X.Modules}
      [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) [Epi φ],
      SchemeOver.IsClosedImmersion (AlgebraicGeometry.AlgebraicSpace.Quot.precompHom f φ))
