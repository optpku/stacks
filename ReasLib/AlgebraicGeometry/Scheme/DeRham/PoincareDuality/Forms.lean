/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower.Multiplication
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.SingleSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.Ext
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- The derived pushforward `Rf_*Ω^p_{X/S}` of relative differential `p`-forms. -/
abbrev pushforwardForm {X S : Scheme.{u}} (f : X ⟶ S) (p : ℕ) :
    RingedSpace.ModuleDerived S.toRingedSpace :=
  (RingedSpace.moduleDerivedPushforward f.toShHom).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj (Λ[p] Ω[f.toShHom]))

namespace PoincareTrace

/-- The endomorphism of `Rf_*Ω^n_{X/S}[n]` induced by multiplication by a global unit on `X`. -/
noncomputable def unitAction {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    (u : Γ(X, ⊤)ˣ) :
    (pushforwardForm f n)⟦(n : ℤ)⟧ ⟶ (pushforwardForm f n)⟦(n : ℤ)⟧ :=
  ((RingedSpace.moduleDerivedPushforward f.toShHom).map
    ((DerivedCategory.singleFunctor X.Modules 0).map
      (RingedSpace.globalSectionMul (u : Γ(X, ⊤)) (Λ[n] Ω[f.toShHom]))))⟦(n : ℤ)⟧'

/-- Multiplication by the unit `1` acts as the identity on the shifted top-form pushforward. -/
theorem unitAction_one {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    unitAction f n (1 : Γ(X, ⊤)ˣ) = 𝟙 _ := sorry

section Pairing

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
variable [HomotopyCategory.KFlat.HasResolutions X.Modules]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom f.toShHom)]
variable [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]

/-- The canonical derived tensor comparison for two relative-form sheaves, with the
ringed-space totalization coherence supplied explicitly. -/
noncomputable def formTensorComparison (p q : ℕ) :=
  @Scheme.Modules.Kunneth.SingleSheaf.tensorComparison X.toRingedSpace
    (inferInstance : RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace)
    (inferInstance : RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace)
    (inferInstance : RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace)
    (inferInstance : HomotopyCategory.KFlat.HasResolutions X.Modules)
    (AlgebraicGeometry.RingedSpace.modulesIntGradedHasTensor X.toRingedSpace)
    (AlgebraicGeometry.RingedSpace.modulesIntGradedHasGoodTensor₁₂Tensor X.toRingedSpace)
    (AlgebraicGeometry.RingedSpace.modulesIntGradedHasGoodTensorTensor₂₃ X.toRingedSpace)
    (AlgebraicGeometry.RingedSpace.modulesIntGradedHasTensor₄ObjExt X.toRingedSpace)
    (Λ[p] Ω[f.toShHom]) (Λ[q] Ω[f.toShHom])

/-- The relative cup product on derived pushforwards of two relative-form sheaves. -/
noncomputable def cupProduct (p q : ℕ) :
    pushforwardForm f p ⊗ pushforwardForm f q ⟶ pushforwardForm f (p + q) :=
  ((RingedSpace.modulePullbackDerivedPushforwardAdjunction
      f.toShHom).rightAdjointLaxMonoidal).μ
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Λ[p] Ω[f.toShHom]))
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Λ[q] Ω[f.toShHom])) ≫
    (RingedSpace.moduleDerivedPushforward f.toShHom).map
      (formTensorComparison f p q ≫
        (DerivedCategory.singleFunctor X.Modules 0).map
          (RingedSpace.ExteriorPower.mul Ω[f.toShHom] p q))

/-- The relative cup product is the pushforward tensorator followed by the degree-zero tensor
comparison and exterior multiplication. -/
theorem cupProduct_eq (p q : ℕ) :
    cupProduct f p q =
      ((RingedSpace.modulePullbackDerivedPushforwardAdjunction
          f.toShHom).rightAdjointLaxMonoidal).μ
          ((DerivedCategory.singleFunctor X.Modules 0).obj (Λ[p] Ω[f.toShHom]))
          ((DerivedCategory.singleFunctor X.Modules 0).obj (Λ[q] Ω[f.toShHom])) ≫
        (RingedSpace.moduleDerivedPushforward f.toShHom).map
          (formTensorComparison f p q ≫
            (DerivedCategory.singleFunctor X.Modules 0).map
              (RingedSpace.ExteriorPower.mul Ω[f.toShHom] p q)) := sorry

/-- The complementary-degree cup product, shifted by `n` and followed by a trace. -/
noncomputable def pairing (n p : ℕ) (hp : p ≤ n)
    (t : (pushforwardForm f n)⟦(n : ℤ)⟧ ⟶
      𝟙_ (RingedSpace.ModuleDerived S.toRingedSpace)) :
    pushforwardForm f p ⊗ (pushforwardForm f (n - p))⟦(n : ℤ)⟧ ⟶
      𝟙_ (RingedSpace.ModuleDerived S.toRingedSpace) :=
  (((tensoringLeft (RingedSpace.ModuleDerived S.toRingedSpace)).obj
      (pushforwardForm f p)).commShiftIso (n : ℤ)).hom.app
        (pushforwardForm f (n - p)) ≫
    (cupProduct f p (n - p))⟦(n : ℤ)⟧' ≫
    eqToHom (congrArg
      (fun q ↦ (pushforwardForm f q)⟦(n : ℤ)⟧)
      (Nat.add_sub_of_le hp)) ≫ t

/-- The pairing is the shifted complementary-degree cup product followed by the trace. -/
theorem pairing_eq (n p : ℕ) (hp : p ≤ n)
    (t : (pushforwardForm f n)⟦(n : ℤ)⟧ ⟶
      𝟙_ (RingedSpace.ModuleDerived S.toRingedSpace)) :
    pairing f n p hp t =
      (((tensoringLeft (RingedSpace.ModuleDerived S.toRingedSpace)).obj
        (pushforwardForm f p)).commShiftIso (n : ℤ)).hom.app
          (pushforwardForm f (n - p)) ≫
        (cupProduct f p (n - p))⟦(n : ℤ)⟧' ≫
        eqToHom (congrArg
          (fun q ↦ (pushforwardForm f q)⟦(n : ℤ)⟧)
          (Nat.add_sub_of_le hp)) ≫ t := sorry

variable [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]

/-- A trace is perfect when every complementary-degree cup-trace pairing has invertible
source-order curry. -/
def IsPerfect (n : ℕ)
    (t : (pushforwardForm f n)⟦(n : ℤ)⟧ ⟶
      𝟙_ (RingedSpace.ModuleDerived S.toRingedSpace)) : Prop :=
  ∀ p : ℕ, ∀ hp : p ≤ n,
    IsIso (braidedHomEquiv
      (pushforwardForm f p) ((pushforwardForm f (n - p))⟦(n : ℤ)⟧)
      (𝟙_ (RingedSpace.ModuleDerived S.toRingedSpace))
      (pairing f n p hp t))

/-- Perfectness of a trace is exactly degreewise invertibility of the curried cup-trace
pairings. -/
theorem isPerfect_iff (n : ℕ)
    (t : (pushforwardForm f n)⟦(n : ℤ)⟧ ⟶
      𝟙_ (RingedSpace.ModuleDerived S.toRingedSpace)) :
    IsPerfect f n t ↔
      ∀ p : ℕ, ∀ hp : p ≤ n,
        IsIso (braidedHomEquiv
          (pushforwardForm f p) ((pushforwardForm f (n - p))⟦(n : ℤ)⟧)
          (𝟙_ (RingedSpace.ModuleDerived S.toRingedSpace))
          (pairing f n p hp t)) := sorry

end Pairing

end PoincareTrace

variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
variable [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Smooth f]
variable [Scheme.Hom.RelativeDimension f n]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
variable [HomotopyCategory.KFlat.HasResolutions X.Modules]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom f.toShHom)]
variable [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
variable [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]

/-- A proper smooth family with nonempty fibres of relative dimension `n` admits a trace on
shifted top forms whose complementary-degree cup-product pairings are perfect. -/
theorem existsPoincareTrace
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) :
    ∃ t : (pushforwardForm f n)⟦(n : ℤ)⟧ ⟶
        𝟙_ (RingedSpace.ModuleDerived S.toRingedSpace),
      PoincareTrace.IsPerfect f n t := sorry

/-- Any two perfect traces for a proper smooth family with nonempty fibres differ by
precomposition with multiplication by a global unit on the source. -/
theorem poincareTrace_unique
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s))
    (t t' : (pushforwardForm f n)⟦(n : ℤ)⟧ ⟶
      𝟙_ (RingedSpace.ModuleDerived S.toRingedSpace))
    (ht : PoincareTrace.IsPerfect f n t)
    (ht' : PoincareTrace.IsPerfect f n t') :
    ∃ u : Γ(X, ⊤)ˣ, t' = PoincareTrace.unitAction f n u ≫ t := sorry

end AlgebraicGeometry.Scheme.DeRham
