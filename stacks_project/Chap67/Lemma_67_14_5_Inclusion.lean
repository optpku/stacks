module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Inclusion

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

#check
  (AlgebraicGeometry.AlgebraicSpace.vanishes_of_le :
    ∀ {Y : AlgebraicSpace S} {I J : IdealSubobject X}, I ≤ J →
      ∀ {f : Y ⟶ X}, vanishes f J → vanishes f I)

#check
  (AlgebraicGeometry.AlgebraicSpace.inclusion :
    ∀ {I J : IdealSubobject X} [IsQuasiCoherent I] [IsQuasiCoherent J],
      I ≤ J → (subscheme J ⟶ subscheme I))

#check
  (AlgebraicGeometry.AlgebraicSpace.inclusion_app :
    ∀ {I J : IdealSubobject X} [IsQuasiCoherent I] [IsQuasiCoherent J]
      (h : I ≤ J) (T : (Over S)ᵒᵖ) (p : (subschemeFunctor J).obj T),
      (inclusion h).app T p = ⟨p.val, vanishes_of_le h p.property⟩)

#check
  (AlgebraicGeometry.AlgebraicSpace.inclusion_subschemeι :
    ∀ {I J : IdealSubobject X} [IsQuasiCoherent I] [IsQuasiCoherent J]
      (h : I ≤ J), inclusion h ≫ subschemeι I = subschemeι J)

#check
  (AlgebraicGeometry.AlgebraicSpace.instIsClosedImmersion_inclusion :
    ∀ {I J : IdealSubobject X} [IsQuasiCoherent I] [IsQuasiCoherent J]
      (h : I ≤ J), IsClosedImmersion (inclusion h))

end AlgebraicGeometry.AlgebraicSpace
