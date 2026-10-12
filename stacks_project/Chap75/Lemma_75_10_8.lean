/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_10_8_Glueing

/-!
# Glueing in `D(𝒪)` along an elementary distinguished square

Lemma 75.10.8: objects of `D(𝒪_U)` and `D(𝒪_V)` with an overlap isomorphism on
`W = U ×_X V` glue to an object of `D(𝒪_X)`, and compatible morphisms into the
restrictions of a test object glue to a morphism out of that glued object.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {U V X : AlgebraicSpace S}
variable (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
variable [IsElementaryDistinguishedSquare j f]
variable [(restrictFunctor (fiberHom j f)).Additive]
variable [(restrictFunctor j).Additive] [(restrictFunctor f).Additive]
variable [(restrictFunctor (Limits.pullback.fst j f)).Additive]
variable [(restrictFunctor (Limits.pullback.snd j f)).Additive]
variable [(restrictFunctor (Limits.pullback.snd j f ≫ f)).Additive]
variable [PreservesFiniteLimits (restrictFunctor (fiberHom j f))]
variable [PreservesFiniteColimits (restrictFunctor (fiberHom j f))]
variable [PreservesFiniteLimits (restrictFunctor j)]
variable [PreservesFiniteColimits (restrictFunctor j)]
variable [PreservesFiniteLimits (restrictFunctor f)]
variable [PreservesFiniteColimits (restrictFunctor f)]
variable [PreservesFiniteLimits (restrictFunctor (Limits.pullback.fst j f))]
variable [PreservesFiniteColimits (restrictFunctor (Limits.pullback.fst j f))]
variable [PreservesFiniteLimits (restrictFunctor (Limits.pullback.snd j f))]
variable [PreservesFiniteColimits (restrictFunctor (Limits.pullback.snd j f))]
variable [PreservesFiniteLimits (restrictFunctor (Limits.pullback.snd j f ≫ f))]
variable [PreservesFiniteColimits (restrictFunctor (Limits.pullback.snd j f ≫ f))]

/-- Lemma 75.10.8 (1). Let `S` be a scheme. Let `(U ⊂ X, V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. Given an object `A` of `D(𝒪_U)`,
an object `B` of `D(𝒪_V)`, and an isomorphism `c : A|_W ⟶ B|_W` on `W = U ×_X V`,
there exists an object `F` of `D(𝒪_X)` and isomorphisms `f : F|_U ⟶ A`,
`g : F|_V ⟶ B` such that `c = g|_W ∘ f⁻¹|_W`. -/
@[stacks 08HB]
theorem exists_moduleDerivedGlue (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    ∃ (eU : (restrictFunctorDerived j).obj (moduleDerivedGlue j f A B c) ≅ A)
      (eV : (restrictFunctorDerived f).obj (moduleDerivedGlue j f A B c) ≅ B),
      c.hom =
        (restrictFunctorDerived (Limits.pullback.fst j f)).map eU.inv ≫
          (moduleDerivedGlueOverlapIso j f A B c).hom ≫
          (restrictFunctorDerived (Limits.pullback.snd j f)).map eV.hom :=
  sorry

/-- Lemma 75.10.8 (2). Let `S` be a scheme. Let `(U ⊂ X, V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. Given glueing data `(A, B, c)` as
in (1), an object `E` of `D(𝒪_X)`, and morphisms `a : A ⟶ E|_U`, `b : B ⟶ E|_V`
with `a|_W = b|_W ∘ c`, there exists a morphism `F ⟶ E` in `D(𝒪_X)` whose
restriction to `U` is `a ∘ f` and whose restriction to `V` is `b ∘ g`. -/
@[stacks 08HB]
theorem exists_moduleDerivedGlueHom (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B)
    (E : ModuleDerived X) (a : A ⟶ (restrictFunctorDerived j).obj E)
    (b : B ⟶ (restrictFunctorDerived f).obj E)
    (hab : moduleDerivedGlueHomCompatible j f A B c E a b) :
    ∃ φ : moduleDerivedGlue j f A B c ⟶ E,
      (restrictFunctorDerived j).map φ = moduleDerivedGlueHomU j f A B c ≫ a ∧
        (restrictFunctorDerived f).map φ = moduleDerivedGlueHomV j f A B c ≫ b :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
