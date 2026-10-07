module

public import stacks_project.Chap75.Definition_75_9_1_Square
public import stacks_project.Chap75.Lemma_75_10_3_Composition
public import stacks_project.Chap75.Lemma_75_10_3_Sequence

/-!
# Relative Mayer–Vietoris triangle for derived pushforward

Lemma 75.10.3: along an elementary distinguished square of algebraic spaces and a
morphism `f : X ⟶ Y`, every object of `D(𝒪_X)` determines a functorial distinguished
triangle in `D(𝒪_Y)` with vertices `Rf_* E`, `Ra_*(E|_U) ⊞ Rb_*(E|_V)`, and
`Rc_*(E|_{U ×_X V})`, where `a = j ≫ f`, `b = g ≫ f`, and `c = fiberHom j g ≫ f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 75.10.3 (1). Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `(U ⊂ X, V ⟶ X)` be an elementary distinguished square. Write
`a = j ≫ f`, `b = g ≫ f`, and `c = fiberHom j g ≫ f`. For every object `E` of
`D(𝒪_X)` the triangle
`Rf_* E ⟶ Ra_*(E|_U) ⊞ Rb_*(E|_V) ⟶ Rc_*(E|_{U ×_X V}) ⟶ Rf_* E⟦1⟧`
is distinguished in `D(𝒪_Y)`. -/
@[stacks 08JK]
theorem mayerVietorisRelativePushforward_mem_distTriang {S : Scheme.{u}}
    {U V X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j] (g : V ⟶ X)
    [Etale g] [IsElementaryDistinguishedSquare j g]
    [(restrictFunctor (fiberHom j g)).Additive]
    [(restrictFunctor j).Additive] [(restrictFunctor g).Additive]
    [(pushforward f).Additive] [(pushforward (j ≫ f)).Additive]
    [(pushforward (g ≫ f)).Additive]
    [(pushforward (fiberHom j g ≫ f)).Additive]
    [PreservesFiniteLimits (restrictFunctor (fiberHom j g))]
    [PreservesFiniteColimits (restrictFunctor (fiberHom j g))]
    [PreservesFiniteLimits (restrictFunctor j)]
    [PreservesFiniteColimits (restrictFunctor j)]
    [PreservesFiniteLimits (restrictFunctor g)]
    [PreservesFiniteColimits (restrictFunctor g)]
    (E : ModuleDerived X) :
    mayerVietorisRelativePushforwardTriangle f j g E ∈ distTriang (ModuleDerived Y) :=
  sorry

/-- Lemma 75.10.3 (2). Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `(U ⊂ X, V ⟶ X)` be an elementary distinguished square. Write
`a = j ≫ f`, `b = g ≫ f`, and `c = fiberHom j g ≫ f`. The distinguished triangle
`Rf_* E ⟶ Ra_*(E|_U) ⊞ Rb_*(E|_V) ⟶ Rc_*(E|_{U ×_X V}) ⟶ Rf_* E⟦1⟧`
of Lemma 75.10.3 (1) is functorial in `E`. -/
@[stacks 08JK]
theorem mayerVietorisRelativePushforwardTriangleFunctor_obj {S : Scheme.{u}}
    {U V X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j] (g : V ⟶ X)
    [Etale g] [IsElementaryDistinguishedSquare j g]
    [(restrictFunctor (fiberHom j g)).Additive]
    [(restrictFunctor j).Additive] [(restrictFunctor g).Additive]
    [(pushforward f).Additive] [(pushforward (j ≫ f)).Additive]
    [(pushforward (g ≫ f)).Additive]
    [(pushforward (fiberHom j g ≫ f)).Additive]
    [PreservesFiniteLimits (restrictFunctor (fiberHom j g))]
    [PreservesFiniteColimits (restrictFunctor (fiberHom j g))]
    [PreservesFiniteLimits (restrictFunctor j)]
    [PreservesFiniteColimits (restrictFunctor j)]
    [PreservesFiniteLimits (restrictFunctor g)]
    [PreservesFiniteColimits (restrictFunctor g)]
    (E : ModuleDerived X) :
    (mayerVietorisRelativePushforwardTriangleFunctor f j g).obj E =
      mayerVietorisRelativePushforwardTriangle f j g E :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
