module

public import stacks_project.Chap75.Definition_75_9_1_Square
public import stacks_project.Chap75.Lemma_75_10_2_Sequence

/-!
# Mayer–Vietoris sequence for étale pushforward

Lemma 75.10.2: along an elementary distinguished square of algebraic spaces,
étale direct image of an `𝒪_X`-module yields a short exact sequence, and the same
maps give a distinguished triangle in `D(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 75.10.2 (1). Let `S` be a scheme. Let `(U ⊂ X, V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. For a sheaf of `𝒪_X`-modules
`F` the sequence
`0 ⟶ F ⟶ j_{U,*} F|_U ⊞ j_{V,*} F|_V ⟶ j_{U×_X V,*} F|_{U×_X V} ⟶ 0`
is short exact. -/
@[stacks 08GW]
theorem mayerVietorisPushforward_shortExact {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (F : X.Modules) :
    (mayerVietorisPushforwardShortComplex j f F).ShortExact :=
  sorry

/-- Lemma 75.10.2 (2). Let `S` be a scheme. Let `(U ⊂ X, V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. For an object `E` of `D(𝒪_X)`
the triangle
`E ⟶ Rj_{U,*} E|_U ⊞ Rj_{V,*} E|_V ⟶ Rj_{U×_X V,*} E|_{U×_X V} ⟶ E⟦1⟧`
is distinguished in `D(𝒪_X)`. -/
@[stacks 08GW]
theorem mayerVietorisPushforward_mem_distTriang {S : Scheme.{u}}
    {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f]
    [(restrictFunctor (fiberHom j f)).Additive]
    [(restrictFunctor j).Additive] [(restrictFunctor f).Additive]
    [PreservesFiniteLimits (restrictFunctor (fiberHom j f))]
    [PreservesFiniteColimits (restrictFunctor (fiberHom j f))]
    [PreservesFiniteLimits (restrictFunctor j)]
    [PreservesFiniteColimits (restrictFunctor j)]
    [PreservesFiniteLimits (restrictFunctor f)]
    [PreservesFiniteColimits (restrictFunctor f)]
    (E : ModuleDerived X) :
    mayerVietorisPushforwardTriangle j f E ∈ distTriang (ModuleDerived X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
