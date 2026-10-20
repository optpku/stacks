module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule
public import ReasLib.Algebra.Homology.DifferentialGradedModule.QuasiIso

/-!
# Quasi-Isomorphisms of Differential Graded Bimodules

Quasi-isomorphisms of DG bimodules are detected on the underlying right-module complexes. The
definition is exposed as a morphism property, so it can be reused directly by localization and
derived-functor APIs.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory
open DifferentialGradedCategory

namespace DifferentialGradedBimodule

variable {R : Type u} [CommRing R]

/-- The morphism property of quasi-isomorphisms of differential graded `(A, B)`-bimodules,
detected after restriction to right DG `B`-modules. -/
@[stacks 09ST "quasi-isomorphisms of differential graded bimodules"]
def quasiIso (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    MorphismProperty (DifferentialGradedBimodule.{u, v, w, x} A B) :=
  (DifferentialGradedModule.quasiIso B).inverseImage
    (forgetToRightModule A B ⋙ DifferentialGradedModule.toK B)

/-- A bimodule morphism is a quasi-isomorphism exactly when its underlying right-module map is
a quasi-isomorphism in `K(B)`. -/
@[stacks 09ST "right-module criterion for bimodule quasi-isomorphisms"]
theorem quasiIso_iff {A : CochainDGAlgebra.{u, w} R}
    {B : CochainDGAlgebra.{u, x} R}
    {T T' : DifferentialGradedBimodule.{u, v, w, x} A B} (f : T ⟶ T') :
    quasiIso A B f ↔ DifferentialGradedModule.quasiIso B
      ((forgetToRightModule A B ⋙ DifferentialGradedModule.toK B).map f) := sorry

/-- Detecting a bimodule quasi-isomorphism after forgetting the left action agrees with
detecting it as a module over the enveloping differential graded algebra. -/
@[stacks 09ST "bimodule quasi-isomorphisms over the enveloping DGA"]
theorem quasiIso_eq_enveloping (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    quasiIso A B =
      (DifferentialGradedModule.quasiIso
        (CochainDGAlgebra.enveloping A B)).inverseImage
          (DifferentialGradedModule.toK
            (CochainDGAlgebra.enveloping A B)) := sorry

end DifferentialGradedBimodule
