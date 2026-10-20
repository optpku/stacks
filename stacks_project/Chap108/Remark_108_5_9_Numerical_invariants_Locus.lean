/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_5_6_Instances
public import stacks_project.Chap75.Lemma_75_26_3_FiberEulerCharacteristic
public import stacks_project.Chap99.«99_8_1_1_Functor»
public import stacks_project.Chap108.Lemma_108_4_9_TensorPower

/-!
# Numerical loci of the Grothendieck Quot functor

The forgetful `T`-point map `Quot_{F/X/B} ⟶ Coh_{X/B}` sends a quotient
`F_T ⟶ Q` to the sheaf `Q`. The numerical locus `Quot^P_{F/X/B}` is the
subfunctor of `quot` on classes whose forgotten sheaf has Euler characteristics
`χ_i = P i`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.DerivedCategory CategoryTheory.DerivedCategory.DerivedTensor
open CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open ComplexShape
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Underived module pullback along a morphism of algebraic spaces is additive. -/
instance instAdditive_modulePullback {Y Z : AlgebraicSpace S} (g : Y ⟶ Z) :
    (pullback g).Additive :=
  sorry

/-- Homotopy-to-derived module pullback has a total left derived functor. -/
instance instHasLeftDerivedFunctor_modulePullback {Y Z : AlgebraicSpace S}
    (g : Y ⟶ Z) :
    (Functor.Homotopy.toDerived (pullback g)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules Z) (up ℤ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The forgetful `T`-point map sending a quotient `F_T ⟶ Q` to the coherent
sheaf `Q` on the fibre `X_T`. -/
def QuotPoint.toObj {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) : (fiber f σ).Modules :=
  Q.point.module

/-- `QuotPoint.toObj Q` is the target module of `Q`. -/
theorem QuotPoint.toObj_eq {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) :
    Q.toObj = Q.point.module :=
  sorry

/-- The forgotten sheaf of a Quot-point is the target of the epimorphism
`F_T ⟶ Q`. -/
theorem QuotPoint.toObj_spec {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) :
    Q.toObj = Q.point.module ∧ Epi Q.point.map :=
  sorry

/-- Kernel-identified Quot-points determine isomorphic forgotten sheaves. -/
theorem QuotPoint.toObj_iso_of_rel {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] (Q₁ Q₂ : QuotPoint f F σ)
    (h : Rel Q₁.point Q₂.point) :
    Nonempty (Q₁.toObj ≅ Q₂.toObj) :=
  sorry

/-- Derived tensor of a derived module with an `𝒪`-module placed in degree 0. -/
def tensorSingle {Y : AlgebraicSpace S} (K : ModuleDerived Y) (F : Y.Modules) :
    ModuleDerived Y :=
  Right.obj K ((DerivedCategory.singleFunctor Y.Modules (0 : ℤ)).obj F)

/-- `tensorSingle` is derived tensor with the degree-zero single complex. -/
theorem tensorSingle_eq {Y : AlgebraicSpace S} (K : ModuleDerived Y)
    (F : Y.Modules) :
    tensorSingle K F =
      Right.obj K ((DerivedCategory.singleFunctor Y.Modules (0 : ℤ)).obj F) :=
  sorry

/-- The derived pullback `E_T = L(X_T ⟶ X)^* E` of a derived `𝒪_X`-module to the
fibre `X_T`. -/
def derivedPullback (f : X ⟶ B) (σ : SchemesOver B) (E : ModuleDerived X) :
    ModuleDerived (fiber f σ) :=
  (Functor.LeftDerived.Homotopy.functor
      (Modules.pullback (pullback.fst f σ.hom))).obj E

/-- `derivedPullback` is the total left derived functor of underived pullback
along `X_T ⟶ X`. -/
theorem derivedPullback_eq (f : X ⟶ B) (σ : SchemesOver B) (E : ModuleDerived X) :
    derivedPullback f σ E =
      (Functor.LeftDerived.Homotopy.functor
          (Modules.pullback (pullback.fst f σ.hom))).obj E :=
  sorry

/-- The object `K = Rf_{T,*}(E_T ⊗ᴸ Q[0])` of `D(𝒪_T)` associated to a
Quot-point and a derived `𝒪_X`-module `E`. -/
def QuotPoint.numericalPushforward {f : X ⟶ B} {F : X.Modules}
    {σ : SchemesOver B} [FinitePresentation f] (Q : QuotPoint f F σ)
    (E : ModuleDerived X) :
    ModuleDerived ((ofOverFunctor S).obj σ.left) :=
  (Modules.pushforwardDerived (pullback.snd f σ.hom)).obj
    (tensorSingle (derivedPullback f σ E) Q.toObj)

/-- `numericalPushforward` is derived pushforward of `E_T ⊗ᴸ Q[0]` along
`X_T ⟶ T`. -/
theorem QuotPoint.numericalPushforward_eq {f : X ⟶ B} {F : X.Modules}
    {σ : SchemesOver B} [FinitePresentation f] (Q : QuotPoint f F σ)
    (E : ModuleDerived X) :
    Q.numericalPushforward E =
      (Modules.pushforwardDerived (pullback.snd f σ.hom)).obj
        (tensorSingle (derivedPullback f σ E) Q.toObj) :=
  sorry

/-- The Euler characteristic `χ_E` of `numericalPushforward Q E`, as a function
on the algebraic-space points of the test scheme `T`. -/
def QuotPoint.eulerChar {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) (E : ModuleDerived X) :
    Points ((ofOverFunctor S).obj σ.left) → ℤ :=
  ModuleDerived.fiberEulerChar (Q.numericalPushforward E)

/-- The value of `eulerChar` at a point is the derived-fiber Euler characteristic
of `numericalPushforward`. -/
theorem QuotPoint.eulerChar_apply {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) (E : ModuleDerived X)
    (t : Points ((ofOverFunctor S).obj σ.left)) :
    Q.eulerChar E t = ModuleDerived.fiberEulerChar (Q.numericalPushforward E) t :=
  sorry

/-- A Quot-point has numerical invariants `P` with respect to `E` if
`χ_i(t) = P i` at every index and every point of the test scheme. -/
def QuotPoint.HasNumerical {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] {I : Type u} (Q : QuotPoint f F σ)
    (E : I → ModuleDerived X) (P : I → ℤ) : Prop :=
  ∀ i t, Q.eulerChar (E i) t = P i

/-- `HasNumerical` unpacks as the pointwise Euler-characteristic condition. -/
theorem QuotPoint.hasNumerical_iff {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] {I : Type u} (Q : QuotPoint f F σ)
    (E : I → ModuleDerived X) (P : I → ℤ) :
    Q.HasNumerical E P ↔ ∀ i t, Q.eulerChar (E i) t = P i :=
  sorry

/-- The numerical locus `Quot^P_{F/X/B}` inside `Quot_{F/X/B}`, as the subfunctor
of kernel-identified classes whose forgotten sheaf has numerical invariants `P`
with respect to a family of perfect derived modules `E`. -/
def quotNumerical (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Subfunctor (quot f F) where
  obj σ :=
    setOf fun q ↦
      ∃ Q : QuotPoint f F σ.unop,
        _root_.Quotient.mk (quotSetoid f F σ.unop) Q = q ∧
          Q.HasNumerical E P
  map := sorry

/-- A class lies in `quotNumerical` if and only if some representing Quot-point
has numerical invariants `P` with respect to `E`. -/
theorem mem_quotNumerical (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) {σ : (SchemesOver B)ᵒᵖ}
    (q : (quot f F).obj σ) :
    q ∈ (quotNumerical f F E P hE).obj σ ↔
      ∃ Q : QuotPoint f F σ.unop,
        _root_.Quotient.mk (quotSetoid f F σ.unop) Q = q ∧
          Q.HasNumerical E P :=
  sorry

/-- The inclusion of the numerical locus into the ambient Quot functor. -/
def quotNumericalι (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    (quotNumerical f F E P hE).toFunctor ⟶ quot f F :=
  (quotNumerical f F E P hE).ι

/-- `quotNumericalι` is the subfunctor inclusion of `quotNumerical`. -/
theorem quotNumericalι_eq (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    quotNumericalι f F E P hE = (quotNumerical f F E P hE).ι :=
  sorry

/-- The derived family `n ↦ L^{⊗ n}` on `ULift ℤ`. -/
def invertiblePowerFamily (L : X.Modules) [isInvertibleObject L] :
    ULift.{u, 0} ℤ → ModuleDerived X :=
  fun n ↦ ModuleDerived.tensorPowerInt
    ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj L) n.down

/-- Evaluating `invertiblePowerFamily L` at `⟨n⟩` recovers the integral derived
tensor power of `L[0]`. -/
theorem invertiblePowerFamily_apply (L : X.Modules) [isInvertibleObject L]
    (n : ℤ) :
    invertiblePowerFamily L (⟨n⟩ : ULift.{u, 0} ℤ) =
      ModuleDerived.tensorPowerInt
        ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj L) n :=
  sorry

/-- Integral derived tensor powers of an invertible `𝒪_X`-module remain perfect. -/
theorem isPerfect_invertiblePowerFamily (L : X.Modules) [isInvertibleObject L]
    (n : ULift.{u, 0} ℤ) :
    ModuleDerived.IsPerfect (invertiblePowerFamily L n) :=
  sorry

/-- The Hilbert numerical locus `Quot^{P,L}_{F/X/B}` of the family
`n ↦ L^{⊗ n}`. -/
abbrev quotNumericalHilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ) :=
  quotNumerical f F (invertiblePowerFamily L) (fun n ↦ P n.down)
    (isPerfect_invertiblePowerFamily L)

/-- `quotNumericalHilbert` is `quotNumerical` of `invertiblePowerFamily L`. -/
theorem quotNumericalHilbert_eq (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L]
    (P : ℤ → ℤ) :
    quotNumericalHilbert f F L P =
      quotNumerical f F (invertiblePowerFamily L) (fun n ↦ P n.down)
        (isPerfect_invertiblePowerFamily L) :=
  sorry

/-- A morphism of `Type (u + 1)` functors on schemes over `B` is flat when it is
relatively representable with respect to `uliftYoneda` and every represented
pullback is a flat morphism of schemes. -/
def IsFlatOnSchemesOver {F G : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) : Prop :=
  let P : MorphismProperty (SchemesOver B) :=
    fun _ _ h ↦ AlgebraicGeometry.Flat h.left.left
  P.relative uliftYoneda.{u + 1} φ

/-- Flatness of Quot-sized functors is relative representability for
`uliftYoneda` together with flatness of every represented scheme map. -/
theorem isFlatOnSchemesOver_iff {F G : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) :
    IsFlatOnSchemesOver φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemesOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.Flat snd.left.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
