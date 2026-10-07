module

public import stacks_project.Chap75.Definition_75_9_1_Square
public import stacks_project.Chap75.Lemma_75_10_1_Sequence

/-!
# Mayer–Vietoris sequence for étale lower shriek

Lemma 75.10.1: along an elementary distinguished square of algebraic spaces,
étale extension by zero of an `𝒪_X`-module yields a short exact sequence, and
the same maps give a distinguished triangle in `D(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 75.10.1 (1). Let `S` be a scheme. Let `(U ⊂ X, V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. For a sheaf of `𝒪_X`-modules
`F` the sequence
`0 ⟶ j_{U×_X V!} F|_{U×_X V} ⟶ j_{U!} F|_U ⊞ j_{V!} F|_V ⟶ F ⟶ 0`
is short exact. -/
@[stacks 08GV]
theorem mayerVietorisLowerShriek_shortExact {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (F : X.Modules) :
    (mayerVietorisLowerShriekShortComplex j f F).ShortExact :=
  sorry

/-- Lemma 75.10.1 (2). Let `S` be a scheme. Let `(U ⊂ X, V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. For an object `E` of `D(𝒪_X)`
the triangle
`j_{U×_X V!} E|_{U×_X V} ⟶ j_{U!} E|_U ⊞ j_{V!} E|_V ⟶ E ⟶ j_{U×_X V!} E|_{U×_X V}⟦1⟧`
is distinguished in `D(𝒪_X)`. -/
@[stacks 08GV]
theorem mayerVietorisLowerShriek_mem_distTriang {S : Scheme.{u}}
    {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f]
    [(restrictFunctor (fiberHom j f)).Additive] [(lowerShriek (fiberHom j f)).Additive]
    [(restrictFunctor j).Additive] [(lowerShriek j).Additive]
    [(restrictFunctor f).Additive] [(lowerShriek f).Additive]
    [(restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f)).Additive]
    [(restrictFunctor j ⋙ lowerShriek j).Additive]
    [(restrictFunctor f ⋙ lowerShriek f).Additive]
    [PreservesFiniteLimits (restrictFunctor (fiberHom j f))]
    [PreservesFiniteColimits (restrictFunctor (fiberHom j f))]
    [PreservesFiniteLimits (lowerShriek (fiberHom j f))]
    [PreservesFiniteColimits (lowerShriek (fiberHom j f))]
    [PreservesFiniteLimits (restrictFunctor j)]
    [PreservesFiniteColimits (restrictFunctor j)]
    [PreservesFiniteLimits (lowerShriek j)]
    [PreservesFiniteColimits (lowerShriek j)]
    [PreservesFiniteLimits (restrictFunctor f)]
    [PreservesFiniteColimits (restrictFunctor f)]
    [PreservesFiniteLimits (lowerShriek f)]
    [PreservesFiniteColimits (lowerShriek f)]
    (E : ModuleDerived X) :
    mayerVietorisLowerShriekTriangle j f E
        (mayerVietorisLowerShriekCochain_shortExact j f
          (DerivedCategory.Q.objPreimage E)) ∈
      distTriang (ModuleDerived X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
