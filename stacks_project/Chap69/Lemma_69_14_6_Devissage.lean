module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap67.Lemma_67_15_3_SchemeTheoreticSupport
public import stacks_project.Chap69.Lemma_69_14_5_Devissage

/-!
# Two-out-of-three dévissage of coherent modules on algebraic spaces

A property of coherent modules on a Noetherian algebraic space which satisfies
two-out-of-three on coherent short exact sequences, descends from nonempty finite
self-coproducts, and admits a scheme-theoretic support model on every reduced
closed subspace with irreducible underlying space, holds for every coherent sheaf.
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

/-- A property of module sheaves satisfies two-out-of-three for short exact sequences
of coherent modules. -/
structure DevissageTwoOutOfThree
    {S : Scheme.{u}} {X : AlgebraicSpace S} (P : X.Modules → Prop) : Prop where
  /-- If the left and middle terms satisfy the property, then so does the right term. -/
  right_of_left_middle {C : ShortComplex X.Modules}
    (hC : C.ShortExact)
    (h₁ : C.X₁.IsCoherent) (h₂ : C.X₂.IsCoherent) (h₃ : C.X₃.IsCoherent)
    (hP₁ : P C.X₁) (hP₂ : P C.X₂) : P C.X₃
  /-- If the left and right terms satisfy the property, then so does the middle term. -/
  middle_of_left_right {C : ShortComplex X.Modules}
    (hC : C.ShortExact)
    (h₁ : C.X₁.IsCoherent) (h₂ : C.X₂.IsCoherent) (h₃ : C.X₃.IsCoherent)
    (hP₁ : P C.X₁) (hP₃ : P C.X₃) : P C.X₂
  /-- If the middle and right terms satisfy the property, then so does the left term. -/
  left_of_middle_right {C : ShortComplex X.Modules}
    (hC : C.ShortExact)
    (h₁ : C.X₁.IsCoherent) (h₂ : C.X₂.IsCoherent) (h₃ : C.X₃.IsCoherent)
    (hP₂ : P C.X₂) (hP₃ : P C.X₃) : P C.X₁

/-- Pack the three coherent short exact implications into a two-out-of-three law. -/
def DevissageTwoOutOfThree.of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {P : X.Modules → Prop}
    (h_right :
      ∀ {C : ShortComplex X.Modules}, C.ShortExact →
        C.X₁.IsCoherent → C.X₂.IsCoherent → C.X₃.IsCoherent →
        P C.X₁ → P C.X₂ → P C.X₃)
    (h_middle :
      ∀ {C : ShortComplex X.Modules}, C.ShortExact →
        C.X₁.IsCoherent → C.X₂.IsCoherent → C.X₃.IsCoherent →
        P C.X₁ → P C.X₃ → P C.X₂)
    (h_left :
      ∀ {C : ShortComplex X.Modules}, C.ShortExact →
        C.X₁.IsCoherent → C.X₂.IsCoherent → C.X₃.IsCoherent →
        P C.X₂ → P C.X₃ → P C.X₁) :
    DevissageTwoOutOfThree P where
  right_of_left_middle hC h₁ h₂ h₃ hP₁ hP₂ := h_right hC h₁ h₂ h₃ hP₁ hP₂
  middle_of_left_right hC h₁ h₂ h₃ hP₁ hP₃ := h_middle hC h₁ h₂ h₃ hP₁ hP₃
  left_of_middle_right hC h₁ h₂ h₃ hP₂ hP₃ := h_left hC h₁ h₂ h₃ hP₂ hP₃

/-- The middle-of-left-right clause of two-out-of-three is extension-closure. -/
def DevissageTwoOutOfThree.toShortExactClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    {P : X.Modules → Prop} (hP : DevissageTwoOutOfThree P) :
    DevissageShortExactClosed P :=
  fun hC h₁ h₂ h₃ hP₁ hP₃ ↦ hP.middle_of_left_right hC h₁ h₂ h₃ hP₁ hP₃

/-- Two-out-of-three for coherent short exact sequences is equivalent to the three
quantified implications. -/
theorem devissageTwoOutOfThree_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : X.Modules → Prop) :
    DevissageTwoOutOfThree P ↔
      (∀ {C : ShortComplex X.Modules}, C.ShortExact →
        C.X₁.IsCoherent → C.X₂.IsCoherent → C.X₃.IsCoherent →
        P C.X₁ → P C.X₂ → P C.X₃) ∧
      (∀ {C : ShortComplex X.Modules}, C.ShortExact →
        C.X₁.IsCoherent → C.X₂.IsCoherent → C.X₃.IsCoherent →
        P C.X₁ → P C.X₃ → P C.X₂) ∧
      (∀ {C : ShortComplex X.Modules}, C.ShortExact →
        C.X₁.IsCoherent → C.X₂.IsCoherent → C.X₃.IsCoherent →
        P C.X₂ → P C.X₃ → P C.X₁) :=
  sorry

/-- A scheme-theoretic support model for a property of coherent modules on `X` is a
coherent sheaf `G` on `X` whose scheme-theoretic support is `i : Z ⟶ X` and which
satisfies `P`. -/
def DevissageSchemeTheoreticSupportModel {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) (P : X.Modules → Prop) : Prop :=
  ∃ G : X.Modules, G.IsCoherent ∧ IsSchemeTheoreticSupport G i ∧ P G

/-- The scheme-theoretic support model condition is equivalent to the existence of a
coherent sheaf on `X` supported at `i` for which `P` holds. -/
theorem devissageSchemeTheoreticSupportModel_iff {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) (P : X.Modules → Prop) :
    DevissageSchemeTheoreticSupportModel i P ↔
      ∃ G : X.Modules, G.IsCoherent ∧ IsSchemeTheoreticSupport G i ∧ P G :=
  sorry

/-- On a Noetherian algebraic space, a property of coherent modules which satisfies
two-out-of-three on coherent short exact sequences, descends from nonempty finite
self-coproducts, contains the zero sheaf, and admits a scheme-theoretic support
model on every reduced closed subspace with irreducible underlying space holds for
every coherent sheaf. -/
theorem devissagePropertyHoldsOfSchemeTheoreticSupportModels
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (P : X.Modules → Prop)
    (h_twoOutOfThree : DevissageTwoOutOfThree P)
    (h_coproduct : DevissageDescendsFromFiniteCoproducts P)
    (h_model : ∀ (Z : AlgebraicSpace S) (i : Z ⟶ X),
      IsClosedImmersion i → IsReduced Z → IsIrreducible Z →
        DevissageSchemeTheoreticSupportModel i P)
    (h_zero : P (0 : X.Modules))
    (F : X.Modules) [F.IsCoherent] :
    P F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
