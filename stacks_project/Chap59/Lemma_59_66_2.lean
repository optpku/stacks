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
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.RelSeries
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Lemma_59_67_1_Degree

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {ℓ : ℕ}

/-- The constant étale sheaf of `F_ℓ`-vector spaces with value `ZMod ℓ`. -/
abbrev constantZModSheaf (T : Scheme.{u})
    [HasWeakSheafify T.smallEtaleTopology (ModuleCat (ZMod ℓ))] :
    Sheaf T.smallEtaleTopology (ModuleCat (ZMod ℓ)) :=
  (constantSheaf T.smallEtaleTopology (ModuleCat (ZMod ℓ))).obj
    (.of (ZMod ℓ) (ZMod ℓ))

/-- Unfolding of `constantZModSheaf` as the constant sheaf on `ModuleCat.of (ZMod ℓ) (ZMod ℓ)`. -/
theorem constantZModSheaf_eq (T : Scheme.{u})
    [HasWeakSheafify T.smallEtaleTopology (ModuleCat (ZMod ℓ))] :
    constantZModSheaf T =
      (constantSheaf T.smallEtaleTopology (ModuleCat (ZMod ℓ))).obj
        (.of (ZMod ℓ) (ZMod ℓ)) := sorry

/-- Inverse image of an étale `F_ℓ`-sheaf along a morphism of schemes. -/
abbrev smallEtaleModuleSheafPullback {S T : Scheme.{u}} (f : T ⟶ S)
    [HasWeakSheafify T.smallEtaleTopology (ModuleCat (ZMod ℓ))]
    [∀ P : S.Etaleᵒᵖ ⥤ ModuleCat (ZMod ℓ),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf S.smallEtaleTopology (ModuleCat (ZMod ℓ))) :
    Sheaf T.smallEtaleTopology (ModuleCat (ZMod ℓ)) :=
  ((smallEtalePullback f).sheafPullback (ModuleCat (ZMod ℓ))
    S.smallEtaleTopology T.smallEtaleTopology).obj F

/-- Unfolding of `smallEtaleModuleSheafPullback` as sheaf pullback along `smallEtalePullback`. -/
theorem smallEtaleModuleSheafPullback_eq {S T : Scheme.{u}} (f : T ⟶ S)
    [HasWeakSheafify T.smallEtaleTopology (ModuleCat (ZMod ℓ))]
    [∀ P : S.Etaleᵒᵖ ⥤ ModuleCat (ZMod ℓ),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf S.smallEtaleTopology (ModuleCat (ZMod ℓ))) :
    smallEtaleModuleSheafPullback f F =
      ((smallEtalePullback f).sheafPullback (ModuleCat (ZMod ℓ))
        S.smallEtaleTopology T.smallEtaleTopology).obj F := sorry

variable {T : Scheme.{u}}
variable {F : Sheaf T.smallEtaleTopology (ModuleCat (ZMod ℓ))}
variable [HasWeakSheafify T.smallEtaleTopology (ModuleCat (ZMod ℓ))]
variable [HasCokernels (Sheaf T.smallEtaleTopology (ModuleCat (ZMod ℓ)))]

/-- Adjacent filtration stages of an étale `F_ℓ`-sheaf whose cokernel is `constantZModSheaf T`. -/
def hasConstantZModSuccessiveQuotient (G H : Subobject F) : Prop :=
  ∃ hle : G ≤ H,
    Nonempty (cokernel (Subobject.ofLE G H hle) ≅ constantZModSheaf T)

/-- A successive quotient is constant of value `ZMod ℓ` exactly when the larger subobject
dominates the smaller one and the cokernel of the inclusion is that constant sheaf. -/
theorem hasConstantZModSuccessiveQuotient_iff (G H : Subobject F) :
    hasConstantZModSuccessiveQuotient G H ↔
      ∃ hle : G ≤ H,
        Nonempty (cokernel (Subobject.ofLE G H hle) ≅ constantZModSheaf T) := sorry

/-- Lemma 59.66.2: on a connected scheme, a finite-type locally constant étale sheaf of
`F_ℓ`-vector spaces pulls back along some finite étale morphism of degree prime to `ℓ`
to a sheaf admitting a finite filtration whose successive quotients are
`constantZModSheaf T`. -/
@[stacks 0A3R]
theorem exists_finiteEtale_pullback_constantZModFiltration
    {S : Scheme.{u}} [ConnectedSpace S] [Fact (Nat.Prime ℓ)]
    [∀ T : Scheme.{u},
      HasWeakSheafify T.smallEtaleTopology (ModuleCat (ZMod ℓ))]
    [∀ (T : Scheme.{u}) (U : T.Etale),
      HasWeakSheafify (T.smallEtaleTopology.over U) (ModuleCat (ZMod ℓ))]
    [∀ {T : Scheme.{u}} (f : T ⟶ S) (P : S.Etaleᵒᵖ ⥤ ModuleCat (ZMod ℓ)),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [∀ T : Scheme.{u},
      HasCokernels (Sheaf T.smallEtaleTopology (ModuleCat (ZMod ℓ)))]
    [∀ T : Scheme.{u},
      HasZeroMorphisms (Sheaf T.smallEtaleTopology (ModuleCat (ZMod ℓ)))]
    (F : Sheaf S.smallEtaleTopology (ModuleCat (ZMod ℓ)))
    [Sheaf.IsFiniteTypeLocallyConstantModule F] :
    ∃ (T : Scheme.{u}) (f : T ⟶ S),
      IsFinite f ∧ Etale f ∧ FiniteEtale.IsConstantDegreePrimeTo f ℓ ∧
        ∃ s : RelSeries
            ({p : Subobject (smallEtaleModuleSheafPullback f F) ×
                Subobject (smallEtaleModuleSheafPullback f F) |
              hasConstantZModSuccessiveQuotient p.1 p.2} : SetRel _ _),
          IsZero (Subobject.underlying.obj s.head) ∧
            Nonempty
              (Subobject.underlying.obj s.last ≅
                smallEtaleModuleSheafPullback f F) := sorry

end AlgebraicGeometry.Scheme
