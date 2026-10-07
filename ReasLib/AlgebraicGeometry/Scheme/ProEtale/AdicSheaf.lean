module

public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ConstructibleModule
public import ReasLib.CategoryTheory.Sites.LocallyIsomorphic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.IdealPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Constant.AdicCompletion

/-!
# Constructible and adic sheaves of Λ-modules on the pro-étale site
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)]
variable [∀ U : X.ProEt, HasWeakSheafify ((topology X).over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
  (baseChange f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((topology Y).over U) (ModuleCat.{w} Λ)]

variable (I : Ideal Λ) (F : Sheaf (topology X) (ModuleCat.{w} Λ))

/-- A sheaf of `Λ`-modules on `X_proétale` is a constructible `Λ`-sheaf
when `F ≅ lim_n F / I^n F` and each `F / I^n F` is a constructible sheaf of `Λ / I^n`-modules,
equivalently a constructible sheaf of `Λ`-modules via the canonical action. -/
class IsConstructibleLambdaSheaf [IsNoetherianRing Λ]
    (I : Ideal Λ) (F : Sheaf (topology X) (ModuleCat.{w} Λ)) : Prop where
  /-- Completeness: the comparison `F ⟶ lim_n F / I^n F` is an isomorphism. -/
  isComplete : IsIso (Sheaf.IdealPower.toLimit I F)
  /-- Each stage `F / I^n F` is a constructible sheaf of modules. -/
  isConstructibleStage : ∀ n : ℕ, IsConstructibleModule (Sheaf.IdealPower.quotient I F n)

/-- Completeness together with stagewise constructibility characterises constructible
`Λ`-sheaves. -/
theorem isConstructibleLambdaSheaf_iff :
    IsConstructibleLambdaSheaf I F ↔
      IsIso (Sheaf.IdealPower.toLimit I F) ∧
        ∀ n : ℕ, IsConstructibleModule (Sheaf.IdealPower.quotient I F n) := sorry

/-- The defining conditions of a constructible `Λ`-sheaf. -/
theorem IsConstructibleLambdaSheaf.spec [IsConstructibleLambdaSheaf I F] :
    IsIso (Sheaf.IdealPower.toLimit I F) ∧
      ∀ n : ℕ, IsConstructibleModule (Sheaf.IdealPower.quotient I F n) := sorry

/-- A constructible `Λ`-sheaf is lisse when each stage `F / I^n F` is
locally constant. -/
class IsLisse [IsNoetherianRing Λ]
    (I : Ideal Λ) (F : Sheaf (topology X) (ModuleCat.{w} Λ)) : Prop
    extends IsConstructibleLambdaSheaf I F where
  /-- Each stage `F / I^n F` is locally constant. -/
  isLocallyConstantStage : ∀ n : ℕ, Sheaf.IsLocallyConstant (Sheaf.IdealPower.quotient I F n)

/-- A sheaf is lisse iff it is a constructible `Λ`-sheaf with locally constant stages. -/
theorem isLisse_iff :
    IsLisse I F ↔
      IsConstructibleLambdaSheaf I F ∧
        ∀ n : ℕ, Sheaf.IsLocallyConstant (Sheaf.IdealPower.quotient I F n) := sorry

/-- The defining conditions of a lisse constructible `Λ`-sheaf. -/
theorem IsLisse.spec [IsLisse I F] :
    IsConstructibleLambdaSheaf I F ∧
      ∀ n : ℕ, Sheaf.IsLocallyConstant (Sheaf.IdealPower.quotient I F n) := sorry

/-- A sheaf of `Λ`-modules on `X_proétale` is adic lisse when it is
locally isomorphic to `underline{M}^∧ = lim_n underline{M / I^n M}` for some `I`-adically
complete `Λ`-module `M` with `M / I M` finite. -/
class IsAdicLisse [IsNoetherianRing Λ]
    (I : Ideal Λ) (F : Sheaf (topology X) (ModuleCat.{w} Λ)) : Prop where
  /-- There exists a complete finite-reduction model whose completed constant sheaf is locally
  isomorphic to `F`. -/
  existsModel :
    ∃ (M : ModuleCat.{w} Λ),
      IsAdicComplete I M ∧
        Module.Finite Λ (M ⧸ (I • (⊤ : Submodule Λ M))) ∧
          Sheaf.IsLocallyIsomorphic F (ConstantSheaf.AdicCompletion.ofModule (topology X) I M)

/-- Adic lisseness is existence of a complete finite-reduction model with a local isomorphism
to the completed constant sheaf. -/
theorem isAdicLisse_iff :
    IsAdicLisse I F ↔
      ∃ (M : ModuleCat.{w} Λ),
        IsAdicComplete I M ∧
          Module.Finite Λ (M ⧸ (I • (⊤ : Submodule Λ M))) ∧
            Sheaf.IsLocallyIsomorphic F (ConstantSheaf.AdicCompletion.ofModule (topology X) I M) := sorry

/-- The defining conditions of an adic lisse sheaf. -/
theorem IsAdicLisse.spec [IsAdicLisse I F] :
    ∃ (M : ModuleCat.{w} Λ),
      IsAdicComplete I M ∧
        Module.Finite Λ (M ⧸ (I • (⊤ : Submodule Λ M))) ∧
          Sheaf.IsLocallyIsomorphic F (ConstantSheaf.AdicCompletion.ofModule (topology X) I M) := sorry

/-- The completed constant sheaf of an `I`-adically complete finite-reduction module is adic
lisse. -/
instance instIsAdicLisse_constantAdicCompletion (M : ModuleCat.{w} Λ)
    [IsAdicComplete I M] [Module.Finite Λ (M ⧸ (I • (⊤ : Submodule Λ M)))] :
    IsAdicLisse I (ConstantSheaf.AdicCompletion.ofModule (topology X) I M) := sorry

/-- The completed constant sheaf `underline{Λ}^∧` is adic lisse. -/
instance instIsAdicLisse_lambdaHat :
    IsAdicLisse I
      (ConstantSheaf.AdicCompletion.ofModule (topology X) I (ModuleCat.of Λ Λ)) := sorry

/-- A sheaf of `Λ`-modules on `X_proétale` is adic constructible when
every affine open admits a decomposition into constructible locally closed subschemes on which
the restriction is adic lisse. -/
class IsAdicConstructible [IsNoetherianRing Λ]
    (I : Ideal Λ) (F : Sheaf (topology X) (ModuleCat.{w} Λ)) : Prop where
  /-- Affine opens admit finite constructible locally closed strata with adic lisse
  restrictions. -/
  existsAffineStrata :
    ∀ (U : X.Opens), IsAffineOpen U →
      ∃ (Q : LocallyClosedPartition U.toScheme), Q.toSet.Finite ∧
        ∀ (s : Q.toSet),
          Topology.IsConstructible (s : Set U.toScheme) ∧
            let T : LocallyCloseds U.toScheme :=
              ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
            IsAdicLisse I (moduleRestrict (LocallyClosedReduction.ι T ≫ U.ι) F)

/-- Unfolding `IsAdicConstructible` recovers the affine stratification criterion. -/
theorem isAdicConstructible_iff :
    IsAdicConstructible I F ↔
      ∀ (U : X.Opens), IsAffineOpen U →
        ∃ (Q : LocallyClosedPartition U.toScheme), Q.toSet.Finite ∧
          ∀ (s : Q.toSet),
            Topology.IsConstructible (s : Set U.toScheme) ∧
              let T : LocallyCloseds U.toScheme :=
                ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
              IsAdicLisse I (moduleRestrict (LocallyClosedReduction.ι T ≫ U.ι) F) := sorry

/-- The defining conditions of an adic constructible sheaf. -/
theorem IsAdicConstructible.spec [IsAdicConstructible I F] :
    ∀ (U : X.Opens), IsAffineOpen U →
      ∃ (Q : LocallyClosedPartition U.toScheme), Q.toSet.Finite ∧
        ∀ (s : Q.toSet),
          Topology.IsConstructible (s : Set U.toScheme) ∧
            let T : LocallyCloseds U.toScheme :=
              ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
            IsAdicLisse I (moduleRestrict (LocallyClosedReduction.ι T ≫ U.ι) F) := sorry

/-- An adic lisse sheaf is adic constructible. -/
instance instIsAdicConstructible_of_isAdicLisse [IsAdicLisse I F] :
    IsAdicConstructible I F := sorry

/-- The completed constant sheaf `underline{Λ}^∧` is a constructible `Λ`-sheaf. -/
instance instIsConstructibleLambdaSheaf_lambdaHat :
    IsConstructibleLambdaSheaf I
      (ConstantSheaf.AdicCompletion.ofModule (topology X) I (ModuleCat.of Λ Λ)) := sorry

/-- The completed constant sheaf `underline{Λ}^∧` is lisse. -/
instance instIsLisse_lambdaHat :
    IsLisse I
      (ConstantSheaf.AdicCompletion.ofModule (topology X) I (ModuleCat.of Λ Λ)) := sorry

end AlgebraicGeometry.Scheme.ProEt
