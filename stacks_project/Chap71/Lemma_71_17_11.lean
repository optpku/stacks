module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Proper
import StacksCheckRecall

/-!
# Lemma 71.17.11

The blowing-up morphism of an algebraic space in a finite-type quasi-coherent
ideal sheaf is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/- Lemma 71.17.11: let `S` be a scheme, let `X` be an algebraic space over `S`,
and let `I ⊂ 𝒪_X` be a quasi-coherent sheaf of ideals. If `I` is of finite type,
then the blowing-up morphism `π.hom : π.space ⟶ X` of `X` in `I` is proper. -/
@[stacks 085Z] #check (AlgebraicGeometry.AlgebraicSpace.Blowup.proper_of_isFiniteType :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    [IsQuasiCoherent I] [I.toModule.IsFiniteType] (π : Blowup X I), Proper π.hom)

end AlgebraicGeometry.AlgebraicSpace.Blowup
