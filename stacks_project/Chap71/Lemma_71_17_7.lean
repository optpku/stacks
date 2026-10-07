module

public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap71.Definition_71_17_1_Blowup

/-!
# Reducedness of blowups of reduced algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- Lemma 71.17.7: let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `I ⊂ 𝒪_X` be a quasi-coherent sheaf of ideals. If `X` is reduced, then the
blowup of `X` in `I` is reduced. -/
@[stacks 085W]
instance instIsReduced {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I) [IsReduced X] :
    IsReduced π.space := sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
