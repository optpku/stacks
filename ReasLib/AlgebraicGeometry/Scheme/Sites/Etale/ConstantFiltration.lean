/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.RelSeries
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Basic
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteEtaleDegree

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

section ZMod

variable {ℓ : ℕ}

/-- The constant étale sheaf of `F_ℓ`-vector spaces with value `ZMod ℓ`. -/
abbrev constantZModSheaf (T : Scheme.{u})
    [HasWeakSheafify T.smallEtaleTopology (ModuleCat (ZMod ℓ))] :
    Sheaf T.smallEtaleTopology (ModuleCat (ZMod ℓ)) :=
  (constantSheaf T.smallEtaleTopology (ModuleCat (ZMod ℓ))).obj
    (.of (ZMod ℓ) (ZMod ℓ))

/-- The constant rank-one module sheaf is the constant sheaf with value `ZMod ℓ`. -/
theorem constantZModSheaf_eq (T : Scheme.{u})
    [HasWeakSheafify T.smallEtaleTopology (ModuleCat (ZMod ℓ))] :
    constantZModSheaf T =
      (constantSheaf T.smallEtaleTopology (ModuleCat (ZMod ℓ))).obj
        (.of (ZMod ℓ) (ZMod ℓ)) := rfl

/-- Inverse image of an étale `F_ℓ`-sheaf along a morphism of schemes. -/
abbrev smallEtaleModuleSheafPullback {S T : Scheme.{u}} (f : T ⟶ S)
    [HasWeakSheafify T.smallEtaleTopology (ModuleCat (ZMod ℓ))]
    [∀ P : S.Etaleᵒᵖ ⥤ ModuleCat (ZMod ℓ),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf S.smallEtaleTopology (ModuleCat (ZMod ℓ))) :
    Sheaf T.smallEtaleTopology (ModuleCat (ZMod ℓ)) :=
  ((smallEtalePullback f).sheafPullback (ModuleCat (ZMod ℓ))
    S.smallEtaleTopology T.smallEtaleTopology).obj F

/-- Étale inverse image is sheaf pullback along base change on the small étale sites. -/
theorem smallEtaleModuleSheafPullback_eq {S T : Scheme.{u}} (f : T ⟶ S)
    [HasWeakSheafify T.smallEtaleTopology (ModuleCat (ZMod ℓ))]
    [∀ P : S.Etaleᵒᵖ ⥤ ModuleCat (ZMod ℓ),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf S.smallEtaleTopology (ModuleCat (ZMod ℓ))) :
    smallEtaleModuleSheafPullback f F =
      ((smallEtalePullback f).sheafPullback (ModuleCat (ZMod ℓ))
        S.smallEtaleTopology T.smallEtaleTopology).obj F := rfl

variable {T : Scheme.{u}}
variable {F : Sheaf T.smallEtaleTopology (ModuleCat (ZMod ℓ))}
variable [HasWeakSheafify T.smallEtaleTopology (ModuleCat (ZMod ℓ))]

/-- Adjacent filtration stages of an étale `F_ℓ`-sheaf whose cokernel is `constantZModSheaf T`. -/
def hasConstantZModSuccessiveQuotient (G H : Subobject F) : Prop :=
  ∃ hle : G ≤ H,
    Nonempty (cokernel (Subobject.ofLE G H hle) ≅ constantZModSheaf T)

/-- A successive quotient is constant of value `ZMod ℓ` exactly when the larger subobject
dominates the smaller one and the cokernel of the inclusion is that constant sheaf. -/
theorem hasConstantZModSuccessiveQuotient_iff (G H : Subobject F) :
    hasConstantZModSuccessiveQuotient G H ↔
      ∃ hle : G ≤ H,
        Nonempty (cokernel (Subobject.ofLE G H hle) ≅ constantZModSheaf T) := Iff.rfl

/-- On a connected scheme, a finite-type locally constant étale sheaf of
`F_ℓ`-vector spaces pulls back along some finite étale morphism of degree prime to `ℓ`
to a sheaf admitting a finite filtration whose successive quotients are
`constantZModSheaf T`. -/
@[stacks 0A3R]
theorem exists_finiteEtale_pullback_constantZModFiltration
    {S : Scheme.{u}} [ConnectedSpace S] [Fact (Nat.Prime ℓ)]
    [∀ T : Scheme.{u},
      HasWeakSheafify T.smallEtaleTopology (ModuleCat (ZMod ℓ))]
    [∀ U : S.Etale,
      HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat (ZMod ℓ))]
    [∀ {T : Scheme.{u}} (f : T ⟶ S) (P : S.Etaleᵒᵖ ⥤ ModuleCat (ZMod ℓ)),
      (smallEtalePullback f).op.HasLeftKanExtension P]
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

end ZMod

section CommModule

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

/-- Étale inverse image of a sheaf of modules is sheaf pullback along base change
on the small étale sites. -/
theorem smallEtaleCommModuleSheafPullback_eq {S T : Scheme.{u}} (f : T ⟶ S)
    {Λ : Type (u + 1)} [CommRing Λ]
    [HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ P : S.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    smallEtaleCommModuleSheafPullback f F =
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
        S.smallEtaleTopology T.smallEtaleTopology).obj F :=
  rfl

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
  Iff.rfl

/-- On an irreducible geometrically unibranch scheme, a finite-type locally constant
étale sheaf of modules over a Noetherian ring, annihilated by a positive prime power,
pulls back along some finite étale morphism of degree prime to that prime to a sheaf
with a finite filtration whose successive quotients are constant sheaves of finitely
generated modules. -/
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

end CommModule

end AlgebraicGeometry.Scheme
