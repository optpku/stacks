module

public import ReasLib.AlgebraicGeometry.LinearSystem.Bertini
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry TensorProduct

noncomputable section

/- Lemma 33.47.3: if a generating linear system on a scheme smooth over a field induces an
immersion into projective space, then its general scalar-extended divisor is smooth over the
extension field. -/
@[stacks 0FD6] #check
  (@AlgebraicGeometry.LinearSystem.holdsForGeneralVector_fiberDivisorSmooth_of_inducesImmersion :
    ∀ {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] {r : ℕ}
      (X : Over (Spec (CommRingCat.of k))) [Smooth X.hom]
      (L : X.left.Modules) [Scheme.Modules.Invertible L]
      (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
      (b : Module.Basis (Fin r) k V)
      (_ : ProjectiveSpace.VectorSpace.LinearSystem.InducesImmersion X L ψ),
      AlgebraicGeometry.LinearSystem.HoldsForGeneralVector b
        (AlgebraicGeometry.LinearSystem.fiberDivisorSmoothOverFieldOfHom X L ψ b))
