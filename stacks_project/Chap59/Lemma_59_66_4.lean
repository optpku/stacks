/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Order.RelSeries
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap58.Lemma_58_5_2
public import stacks_project.Chap59.Lemma_59_67_1_Degree

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme


/-- Inverse image of an étale sheaf of `Λ`-modules along a morphism of schemes. -/
abbrev smallEtaleCommModuleSheafPullback {S T : Scheme.{u}} (f : T ⟶ S)
    {Λ : Type (u + 1)} [CommRing Λ]
    [HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ P : S.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  ((smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
    S.smallEtaleTopology T.smallEtaleTopology).obj F

/-- Unfolding of `smallEtaleCommModuleSheafPullback` as sheaf pullback along
`smallEtalePullback`. -/
theorem smallEtaleCommModuleSheafPullback_eq {S T : Scheme.{u}} (f : T ⟶ S)
    {Λ : Type (u + 1)} [CommRing Λ]
    [HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ P : S.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    smallEtaleCommModuleSheafPullback f F =
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
        S.smallEtaleTopology T.smallEtaleTopology).obj F :=
  sorry

variable {T : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
variable {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
variable [HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasCokernels (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasZeroObject (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))]

/-- Adjacent filtration stages of an étale sheaf of `Λ`-modules whose cokernel is a
constant sheaf of a finite `Λ`-module. -/
def hasConstantFiniteModuleSuccessiveQuotient (G H : Subobject F) : Prop :=
  ∃ hle : G ≤ H,
    ∃ M : ModuleCat.{u + 1} Λ, Module.Finite Λ M ∧
      Nonempty
        (cokernel (Subobject.ofLE G H hle) ≅
          (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)

/-- A successive quotient is constant of finite type exactly when the larger subobject
dominates the smaller one and the cokernel of the inclusion is the constant sheaf of
some finite `Λ`-module. -/
theorem hasConstantFiniteModuleSuccessiveQuotient_iff (G H : Subobject F) :
    hasConstantFiniteModuleSuccessiveQuotient G H ↔
      ∃ hle : G ≤ H,
        ∃ M : ModuleCat.{u + 1} Λ, Module.Finite Λ M ∧
          Nonempty
            (cokernel (Subobject.ofLE G H hle) ≅
              (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  sorry

/-- Lemma 59.66.4: on an irreducible geometrically unibranch scheme `S`, a finite-type
locally constant étale sheaf of modules over a Noetherian ring `Λ`, annihilated by
`ℓ ^ n`, pulls back along some finite étale morphism of degree prime to `ℓ` to a sheaf
with a finite filtration whose successive quotients are constant sheaves of finite
`Λ`-modules. Here `f⁻¹F` is sheaf pullback along `smallEtalePullback f`, and
`underline M_T` is `(constantSheaf T.smallEtaleTopology (ModuleCat Λ)).obj M`. -/
@[stacks 0GJ0]
theorem exists_finiteEtale_pullback_constant_filtration
    {S : Scheme.{u}} [IrreducibleSpace S] (huni : S.isGeometricallyUnibranch)
    (ell n : ℕ) [Fact (Nat.Prime ell)] (hn : 1 ≤ n)
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    [∀ T : Scheme.{u},
      HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ (T : Scheme.{u}) (U : T.Etale),
      HasWeakSheafify (T.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ {T : Scheme.{u}} (f : T ⟶ S)
      (P : S.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [∀ T : Scheme.{u},
      HasCokernels (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [∀ T : Scheme.{u},
      HasZeroObject (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Sheaf.IsFiniteTypeLocallyConstantModule F]
    (h_ann : (ell ^ n : ℕ) • 𝟙 F = 0) :
    ∃ (T : Scheme.{u}) (f : T ⟶ S),
      finiteEtaleMorphism f ∧ FiniteEtale.IsConstantDegreePrimeTo f ell ∧
        ∃ s : RelSeries
            ({p : Subobject (smallEtaleCommModuleSheafPullback f F) ×
                Subobject (smallEtaleCommModuleSheafPullback f F) |
              hasConstantFiniteModuleSuccessiveQuotient p.1 p.2} : SetRel _ _),
          IsZero (Subobject.underlying.obj s.head) ∧ IsIso s.last.arrow :=
  sorry

end AlgebraicGeometry.Scheme

end
