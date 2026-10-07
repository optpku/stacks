module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_3_1_Restrict

/-!
# Derived étale restriction–pushforward adjunction

An étale morphism `f : V ⟶ X` of algebraic spaces induces `f^* ⊣ Rf_*` on unbounded
derived categories of modules. Restriction is exact, so the left adjoint is
`restrictFunctorDerived`; the right adjoint is the K-injective derived pushforward.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {V X : AlgebraicSpace S}

/-- The unbounded derived adjunction `f^* ⊣ Rf_*` associated to an étale morphism of
algebraic spaces. -/
def restrictPushforwardDerivedAdjunction (f : V ⟶ X) [Etale f] :
    restrictFunctorDerived f ⊣ pushforwardDerived f :=
  Adjunction.Derived.KInjective.adjunction
    (ExactFunctor.of (restrictFunctor f)) (pushforward f) (restrictAdjunction f)

/-- The derived étale restriction–pushforward adjunction is the K-injective derived
adjunction of `restrictAdjunction`. -/
theorem restrictPushforwardDerivedAdjunction_eq (f : V ⟶ X) [Etale f] :
    restrictPushforwardDerivedAdjunction f =
      Adjunction.Derived.KInjective.adjunction
        (ExactFunctor.of (restrictFunctor f)) (pushforward f) (restrictAdjunction f) :=
  sorry

/-- The unit of `restrictPushforwardDerivedAdjunction` at `E` is the adjunct of the
identity on `E|_V`, i.e. the canonical map `E ⟶ Rf_*(E|_V)`. -/
theorem restrictPushforwardDerivedAdjunction_unit_app (f : V ⟶ X) [Etale f]
    (E : ModuleDerived X) :
    (restrictPushforwardDerivedAdjunction f).unit.app E =
      (restrictPushforwardDerivedAdjunction f).homEquiv
        E ((restrictFunctorDerived f).obj E) (𝟙 _) :=
  sorry

/-- The counit of `restrictPushforwardDerivedAdjunction` at `F` is the coadjunct of the
identity on `Rf_* F`, i.e. the canonical map `(Rf_* F)|_V ⟶ F`. -/
theorem restrictPushforwardDerivedAdjunction_counit_app (f : V ⟶ X) [Etale f]
    (F : ModuleDerived V) :
    (restrictPushforwardDerivedAdjunction f).counit.app F =
      ((restrictPushforwardDerivedAdjunction f).homEquiv
        ((pushforwardDerived f).obj F) F).symm (𝟙 _) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
