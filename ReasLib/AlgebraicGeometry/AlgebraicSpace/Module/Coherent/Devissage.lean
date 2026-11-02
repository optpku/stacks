/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Irreducible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure

/-!
# Dévissage of coherent module sheaves on algebraic spaces
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- On a Noetherian algebraic space, a coherent module with reduced irreducible
scheme-theoretic support admits a monomorphism from the pushforward of a positive
finite coproduct of a nonzero coherent ideal on that support, with cokernel supported
on a proper closed subset of the support. -/
@[stacks 07UQ]
theorem exists_coherentIdeal_coproduct_pushforward_mono
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    {Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsSchemeTheoreticSupport F i] [IsReduced Z] [IsIrreducible Z] :
    ∃ (r : ℕ) (I : IdealSubobject Z)
      (φ : (pushforward i).obj (∐ fun _ : Fin r ↦ I.toModule) ⟶ F)
      (W : TopologicalSpace.Closeds (Points X)),
      0 < r ∧ I ≠ ⊥ ∧ I.toModule.IsCoherent ∧
        ((pushforward i).obj (∐ fun _ : Fin r ↦ I.toModule)).IsCoherent ∧
        Mono φ ∧ moduleSupport (cokernel φ) ⊆ (W : Set (Points X)) ∧
          (W : Set (Points X)) ⊂ Set.range (Points.map i) :=
  sorry

/-- On a Noetherian algebraic space, every coherent module admits a finite filtration by
coherent submodules whose successive quotients are pushforwards of coherent ideal sheaves
on reduced irreducible closed subspaces. -/
@[stacks 07UR]
theorem exists_coherentSubobject_filtration_quotient_iso_pushforward_ideal
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent] :
    ∃ (m : ℕ) (Fil : ℕ →o Subobject F) (Z : Fin m → ClosedSubspace X)
      (I : (j : Fin m) → IdealSubobject (Z j).X)
      (e : (j : Fin m) →
        cokernel (Subobject.ofLE (Fil j.1) (Fil (j.1 + 1))
          (Fil.monotone (Nat.le_succ j.1))) ≅
          (pushforward (Z j).ι).obj (I j).toModule),
      ∃ (hBot : Fil 0 = ⊥) (hTop : Fil m = ⊤)
        (hFiltrationCoherent :
          ∀ n, n ≤ m → ((Fil n : Subobject F) : X.Modules).IsCoherent)
        (hReduced : ∀ j : Fin m, IsReduced (Z j).X)
        (hIrreducible : ∀ j : Fin m, IsIrreducible (Z j).X),
        ∀ j : Fin m, (I j).toModule.IsCoherent :=
  sorry

/-- On a Noetherian algebraic space, a property of module sheaves that holds for zero,
is preserved by short exact extensions of coherent sheaves, and holds for pushforwards
of quasi-coherent ideal sheaves from reduced irreducible closed subspaces holds for
every coherent module sheaf. -/
@[stacks 07US]
theorem coherent_property_of_shortExact_and_pushforward_ideal
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (P : X.Modules → Prop)
    (h_zero : P (0 : X.Modules))
    (h_shortExact :
      ∀ {C : ShortComplex X.Modules}, C.ShortExact →
        C.X₁.IsCoherent → C.X₂.IsCoherent → C.X₃.IsCoherent →
        P C.X₁ → P C.X₃ → P C.X₂)
    (h_pushforward_ideal :
      ∀ (Z : AlgebraicSpace S) (i : Z ⟶ X),
        IsClosedImmersion i → IsReduced Z → IsIrreducible Z →
          ∀ (I : IdealSubobject Z), IsQuasiCoherent I →
            P ((pushforward i).obj I.toModule))
    (F : X.Modules) [F.IsCoherent] :
    P F := by
  obtain ⟨m, Fil, Z, I, e, hBot, hTop, hFil, hReduced, hIrreducible, hIdeal⟩ :=
    exists_coherentSubobject_filtration_quotient_iso_pushforward_ideal F
  let eBot : ((Fil 0 : Subobject F) : X.Modules) ≅ 0 :=
    Subobject.isoOfEq _ _ hBot ≪≫ Subobject.botCoeIsoZero
  haveI : ((Fil 0 : Subobject F) : X.Modules).IsCoherent := hFil 0 (Nat.zero_le m)
  haveI : (0 : X.Modules).IsCoherent := SheafOfModules.IsCoherent.of_iso eBot
  -- Extension closure also transports the property across coherent isomorphisms.
  have h_iso : ∀ {A B : X.Modules}, A.IsCoherent → B.IsCoherent →
      (A ≅ B) → P A → P B := by
    intro A B hA hB φ hPA
    let C : ShortComplex X.Modules := ShortComplex.mk φ.hom (0 : B ⟶ 0) (by simp)
    have hC : C.ShortExact :=
      (show C.Splitting from
        { r := φ.inv
          s := 0
          f_r := by simp [C]
          s_g := by simp [C]
          id := by simp [C] }).shortExact
    exact h_shortExact hC hA hB inferInstance hPA h_zero
  have hFilP : ∀ n, n ≤ m → P ((Fil n : Subobject F) : X.Modules) := by
    intro n
    induction n with
    | zero =>
        intro hn
        exact h_iso inferInstance (hFil 0 hn) eBot.symm h_zero
    | succ n ih =>
        intro hn
        have hn' : n ≤ m := (Nat.le_succ n).trans hn
        haveI : ((Fil n : Subobject F) : X.Modules).IsCoherent := hFil n hn'
        haveI : ((Fil (n + 1) : Subobject F) : X.Modules).IsCoherent := hFil (n + 1) hn
        let f := Subobject.ofLE (Fil n) (Fil (n + 1)) (Fil.monotone (Nat.le_succ n))
        haveI : (cokernel f).IsCoherent := SheafOfModules.IsCoherent.cokernel f
        let j : Fin m := ⟨n, Nat.lt_of_succ_le hn⟩
        haveI : (I j).toModule.IsCoherent := hIdeal j
        haveI : ((pushforward (Z j).ι).obj (I j).toModule).IsCoherent :=
          SheafOfModules.IsCoherent.of_iso (e j)
        have hQ : P (cokernel f) :=
          h_iso inferInstance inferInstance (e j).symm
            (h_pushforward_ideal (Z j).X (Z j).ι (Z j).isClosedImmersion
              (hReduced j) (hIrreducible j) (I j) ⟨inferInstance⟩)
        have hC : (ShortComplex.cokernelSequence f).ShortExact :=
          { exact := ShortComplex.cokernelSequence_exact f
            mono_f := by dsimp [ShortComplex.cokernelSequence, f]; infer_instance
            epi_g := by dsimp [ShortComplex.cokernelSequence]; infer_instance }
        exact h_shortExact hC
          (by dsimp [ShortComplex.cokernelSequence]; infer_instance)
          (by dsimp [ShortComplex.cokernelSequence]; infer_instance)
          (by dsimp [ShortComplex.cokernelSequence]; infer_instance) (ih hn') hQ
  exact h_iso (hFil m le_rfl) inferInstance
    (Subobject.isoOfEq _ _ hTop ≪≫ Subobject.underlyingIso (𝟙 F)) (hFilP m le_rfl)

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
  Iff.rfl

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
  Iff.rfl

/-- A reduced irreducible closed model for a property of coherent modules on `X` is a
coherent sheaf `G` on `Z` of full support such that every nonzero quasi-coherent
ideal `I ⊂ 𝒪_Z` admits a quasi-coherent subsheaf `G' ⊂ I G` with the support of
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
            (∀ (τ : TopologicalSpace (Points Z)), IsPointsTopology Z τ →
              @IsClosed (Points Z) τ (moduleSupport (cokernel G'.arrow))) ∧
            P ((pushforward i).obj (G' : Z.Modules))

/-- The reduced closed model condition is equivalent to the existence of a coherent
sheaf of full support on `Z` together with, for every nonzero quasi-coherent ideal,
a quasi-coherent subsheaf `G'` of `I G` whose quotient `G / G'` has proper closed
support and whose pushforward satisfies `P`. -/
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
                (∀ (τ : TopologicalSpace (Points Z)), IsPointsTopology Z τ →
                  @IsClosed (Points Z) τ (moduleSupport (cokernel G'.arrow))) ∧
                P ((pushforward i).obj (G' : Z.Modules)) :=
  Iff.rfl

/-- On a Noetherian algebraic space, an extension-closed property of coherent modules
which contains the zero sheaf, descends from nonempty finite self-coproducts, and
admits a reduced irreducible closed model on every reduced closed subspace with
irreducible underlying space holds for every coherent sheaf. -/
@[stacks 07UT]
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
  ⟨fun hP ↦ ⟨hP.right_of_left_middle, hP.middle_of_left_right,
      hP.left_of_middle_right⟩,
    fun ⟨h_right, h_middle, h_left⟩ ↦ DevissageTwoOutOfThree.of h_right h_middle h_left⟩

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
  Iff.rfl

/-- On a Noetherian algebraic space, a property of coherent modules which satisfies
two-out-of-three on coherent short exact sequences, descends from nonempty finite
self-coproducts, contains the zero sheaf, and admits a scheme-theoretic support
model on every reduced closed subspace with irreducible underlying space holds for
every coherent sheaf. -/
@[stacks 08AN]
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
