module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Representability
import StacksCheckRecall

/-!
# Remark 99.8.5 (Quot via Artin's axioms)

If `S` is a Noetherian scheme with G-ring local rings, `f : X ⟶ S` is a
finitely presented separated morphism of algebraic spaces, and `F` is a
finitely presented quasi-coherent sheaf on `X` flat over `S`, then
`Quot_{F/X/S}` is an algebraic space locally of finite presentation over `S`.

Artin's axioms give a proof via the representable diagonal, the sheaf and limit
conditions, Rim-Schlessinger, finite-dimensional tangent spaces, effectiveness
from Grothendieck existence, and openness of versality from obstruction theory.
This avoids using algebraicity of the stack of coherent sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/- Remark 99.8.5 (Quot via Artin's axioms).
The proper-support Quot functor is an algebraic space locally of finite
presentation over the base under the stated hypotheses. -/
@[stacks 0CZW] #check
  (AlgebraicGeometry.AlgebraicSpace.Quot.isLocallyOfFinitePresentationOver_of_artinAxioms :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] [HasGRingStalks S]
    {X : AlgebraicSpace S} (f : X ⟶ ofOver (Over.mk (𝟙 S)))
    [FinitePresentation f] [Separated f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hF_flat : Modules.flatOver F f),
    IsLocallyOfFinitePresentationOver (quot f F))

end AlgebraicGeometry.AlgebraicSpace.Quot
