module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal

/-!
# Inclusions of closed subspaces of algebraic spaces

A comparison of quasi-coherent ideal sheaves `I ≤ J` induces a morphism
`subscheme J ⟶ subscheme I` of the corresponding closed subspaces, compatible
with the inclusions into the ambient algebraic space.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Vanishing of a larger ideal sheaf along a morphism implies vanishing of a
smaller one. -/
theorem vanishes_of_le {Y : AlgebraicSpace S} {I J : IdealSubobject X} (h : I ≤ J)
    {f : Y ⟶ X} (hf : vanishes f J) : vanishes f I :=
  sorry

/-- The closed-subspace morphism `subscheme J ⟶ subscheme I` induced by `I ≤ J`. -/
def inclusion {I J : IdealSubobject X} [IsQuasiCoherent I] [IsQuasiCoherent J]
    (h : I ≤ J) : subscheme J ⟶ subscheme I where
  app T := TypeCat.ofHom fun p : (subschemeFunctor J).obj T ↦
    ⟨p.val, vanishes_of_le h p.property⟩
  naturality := sorry

/-- On `T`-points, `inclusion h` keeps the underlying point of `X` and weakens the
vanishing witness. -/
theorem inclusion_app {I J : IdealSubobject X} [IsQuasiCoherent I] [IsQuasiCoherent J]
    (h : I ≤ J) (T : (Over S)ᵒᵖ) (p : (subschemeFunctor J).obj T) :
    (inclusion h).app T p = ⟨p.val, vanishes_of_le h p.property⟩ :=
  sorry

/-- The comparison `subscheme J ⟶ subscheme I` commutes with the closed-subspace
inclusions into `X`. -/
theorem inclusion_subschemeι {I J : IdealSubobject X} [IsQuasiCoherent I]
    [IsQuasiCoherent J] (h : I ≤ J) :
    inclusion h ≫ subschemeι I = subschemeι J :=
  sorry

/-- The closed-subspace morphism induced by `I ≤ J` is a closed immersion. -/
instance instIsClosedImmersion_inclusion {I J : IdealSubobject X}
    [IsQuasiCoherent I] [IsQuasiCoherent J] (h : I ≤ J) :
    IsClosedImmersion (inclusion h) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
