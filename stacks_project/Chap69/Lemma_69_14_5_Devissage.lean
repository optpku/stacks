module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject
public import stacks_project.Chap67.Definition_67_47_7_Irreducible
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower

/-!
# Dévissage of coherent modules on algebraic spaces

An extension-closed property of coherent modules on a Noetherian algebraic space
which descends from nonempty finite self-coproducts, and which admits a reduced
irreducible closed model on every reduced closed subspace with irreducible
underlying space, holds for every coherent sheaf.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open scoped ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A property of module sheaves is preserved by short exact extensions of coherent
modules. -/
def DevissageShortExactClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : X.Modules → Prop) : Prop :=
  ∀ {C : ShortComplex X.Modules}, C.ShortExact →
    C.X₁.IsCoherent → C.X₂.IsCoherent → C.X₃.IsCoherent →
    P C.X₁ → P C.X₃ → P C.X₂

/-- Short-exact closure is equivalent to preservation by every coherent short exact
extension. -/
theorem devissageShortExactClosed_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : X.Modules → Prop) :
    DevissageShortExactClosed P ↔
      ∀ {C : ShortComplex X.Modules}, C.ShortExact →
        C.X₁.IsCoherent → C.X₂.IsCoherent → C.X₃.IsCoherent →
        P C.X₁ → P C.X₃ → P C.X₂ :=
  sorry

/-- A property of coherent module sheaves descends from every nonempty finite
self-coproduct. -/
def DevissageDescendsFromFiniteCoproducts {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : X.Modules → Prop) : Prop :=
  ∀ (F : X.Modules), F.IsCoherent → ∀ (r : ℕ), 0 < r →
    P (∐ fun _ : Fin r ↦ F) → P F

/-- Descent from finite self-coproducts is equivalent to descent for every coherent
module and every positive number of summands. -/
theorem devissageDescendsFromFiniteCoproducts_iff
    {S : Scheme.{u}} {X : AlgebraicSpace S} (P : X.Modules → Prop) :
    DevissageDescendsFromFiniteCoproducts P ↔
      ∀ (F : X.Modules), F.IsCoherent → ∀ (r : ℕ), 0 < r →
        P (∐ fun _ : Fin r ↦ F) → P F :=
  sorry

/-- A reduced irreducible closed model for a property of coherent modules on `X` is a
coherent sheaf `G` on `Z` of full support such that every nonzero quasi-coherent
ideal `I ⊂ 𝒪_Z` contains a quasi-coherent subsheaf `G' ⊂ I G` with the support of
`G / G'` a proper closed subset of `|Z|` and with `P` holding for
`(pushforward i).obj G'`. -/
def DevissageReducedClosedModel {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) (P : X.Modules → Prop) : Prop :=
  ∃ (G : Z.Modules), G.IsCoherent ∧
    moduleSupport G = (Set.univ : Set (Points Z)) ∧
      ∀ (I : IdealSubobject Z), IsQuasiCoherent I → I ≠ ⊥ →
        ∃ G' : Subobject G,
          (G' : Z.Modules).IsQuasicoherent ∧
            G' ≤ idealPowerProductSubobject I G 1 ∧
            moduleSupport (cokernel G'.arrow) ⊂ (Set.univ : Set (Points Z)) ∧
            P ((pushforward i).obj (G' : Z.Modules))

/-- The reduced closed model condition is equivalent to the existence of a coherent
sheaf of full support on `Z` together with, for every nonzero quasi-coherent ideal,
a quasi-coherent subsheaf of `I G` of properly smaller support whose pushforward
satisfies `P`. -/
theorem devissageReducedClosedModel_iff {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) (P : X.Modules → Prop) :
    DevissageReducedClosedModel i P ↔
      ∃ (G : Z.Modules), G.IsCoherent ∧
        moduleSupport G = (Set.univ : Set (Points Z)) ∧
          ∀ (I : IdealSubobject Z), IsQuasiCoherent I → I ≠ ⊥ →
            ∃ G' : Subobject G,
              (G' : Z.Modules).IsQuasicoherent ∧
                G' ≤ idealPowerProductSubobject I G 1 ∧
                moduleSupport (cokernel G'.arrow) ⊂
                  (Set.univ : Set (Points Z)) ∧
                P ((pushforward i).obj (G' : Z.Modules)) :=
  sorry

/-- On a Noetherian algebraic space, an extension-closed property of coherent modules
which contains the zero sheaf, descends from nonempty finite self-coproducts, and
admits a reduced irreducible closed model on every reduced closed subspace with
irreducible underlying space holds for every coherent sheaf. -/
theorem devissagePropertyHoldsOfReducedClosedModels
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (P : X.Modules → Prop)
    (h_shortExact : DevissageShortExactClosed P)
    (h_coproduct : DevissageDescendsFromFiniteCoproducts P)
    (h_model : ∀ (Z : AlgebraicSpace S) (i : Z ⟶ X),
      IsClosedImmersion i → IsReduced Z → IsIrreducible Z →
        DevissageReducedClosedModel i P)
    (h_zero : P (0 : X.Modules))
    (F : X.Modules) [F.IsCoherent] :
    P F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
