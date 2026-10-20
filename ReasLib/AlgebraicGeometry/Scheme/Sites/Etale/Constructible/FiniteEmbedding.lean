/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.Topology.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ConstantDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}}

/-- A morphism maps onto a closed irreducible reduced subscheme and is finite étale over a
nonempty open of that subscheme. -/
def mapsOntoClosedFiniteEtaleOverOpen {Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  IrreducibleSpace Y ∧ IsReduced Y ∧
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (g : Y ⟶ Z),
      IsClosedImmersion i ∧ f = g ≫ i ∧ IrreducibleSpace Z ∧ IsReduced Z ∧
        Function.Surjective g.base ∧
          ∃ (U : Z.Opens), Nonempty U ∧
            Etale (pullback.fst (U.ι) g) ∧ IsFinite (pullback.fst (U.ι) g)

section Noetherian

variable [IsNoetherian X]

section SetValued

variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
variable [HasProducts.{0} (Sheaf X.smallEtaleTopology (Type (u + 1)))]

/-- A constructible étale sheaf of sets on a Noetherian scheme embeds into a finite product of
pushforwards of finite constant sheaves with generically finite étale geometric models. -/
theorem IsConstructibleEtaleSet.exists_mono_to_pi_pushforward_constantSheaf
    {F : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (hF : IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstant G) F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X) (E : Fin n → Type (u + 1)),
      (∀ i, IsFinite (f i)) ∧ (∀ i, Finite (E i)) ∧
          (∀ i, mapsOntoClosedFiniteEtaleOverOpen (f i)) ∧
            ∃ φ : F ⟶ ∏ᶜ fun i ↦ pushforwardConstantSheaf (f i) (E i), Mono φ :=
  sorry

end SetValued

section AbelianGroups

variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasCoproducts.{0} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- A constructible étale sheaf of finite abelian groups on a Noetherian scheme embeds into a
finite coproduct of constant-sheaf pushforwards with generically finite étale models. -/
theorem IsConstructibleEtaleAddCommGrp.exists_mono_to_coprod_pushforward_constantSheaf
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleEtaleAddCommGrp
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
      (M : Fin n → AddCommGrpCat.{u + 1}),
      (∀ i, IsFinite (f i)) ∧ (∀ i, Finite (M i)) ∧
          (∀ i, mapsOntoClosedFiniteEtaleOverOpen (f i)) ∧
            ∃ φ : F ⟶ ∐ fun i ↦ pushforwardConstantSheaf (f i) (M i), Mono φ :=
  sorry

end AbelianGroups

section Modules

variable {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
  (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable [HasCoproducts.{0} (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]

/-- A constructible étale sheaf of finite-type modules over a commutative Noetherian ring embeds
into a finite coproduct of constant-sheaf pushforwards with generically finite étale geometric
models. -/
theorem IsConstructibleEtaleModule.exists_mono_to_coprod_pushforward_constantSheaf
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)}
    (hF : IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G) F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
      (M : Fin n → ModuleCat.{w} Λ),
      (∀ i, IsFinite (f i)) ∧ (∀ i, Module.Finite Λ (M i)) ∧
          (∀ i, mapsOntoClosedFiniteEtaleOverOpen (f i)) ∧
            ∃ φ : F ⟶ ∐ fun i ↦ pushforwardConstantSheaf (f i) (M i), Mono φ :=
  sorry

end Modules

end Noetherian

section QuasiCompactQuasiSeparated

variable [CompactSpace X] [QuasiSeparatedSpace X]

section SetValued

variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
variable [HasProducts.{0} (Sheaf X.smallEtaleTopology (Type (u + 1)))]

/-- A constructible étale sheaf of sets on a quasi-compact quasi-separated scheme embeds into
a finite product of pushforwards of finite constant sheaves along finite finitely presented
morphisms. -/
theorem IsConstructibleEtaleSet.exists_mono_to_pi_pushforward_constantSheaf_qcqs
    {F : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (hF : IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstant G) F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X) (E : Fin n → Type (u + 1)),
      (∀ i, IsFinite (f i)) ∧ (∀ i, LocallyOfFinitePresentation (f i)) ∧ (∀ i, Finite (E i)) ∧
        ∃ φ : F ⟶ ∏ᶜ fun i ↦ pushforwardConstantSheaf (f i) (E i), Mono φ :=
  sorry

end SetValued

section AbelianGroups

variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasCoproducts.{0} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- A constructible abelian étale sheaf on a quasi-compact quasi-separated scheme embeds into
a finite coproduct of pushforwards of finite constant abelian sheaves along finite finitely
presented morphisms. -/
theorem IsConstructibleEtaleAddCommGrp.exists_mono_to_coprod_pushforward_constantSheaf_qcqs
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleEtaleAddCommGrp
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
      (M : Fin n → AddCommGrpCat.{u + 1}),
      (∀ i, IsFinite (f i)) ∧ (∀ i, LocallyOfFinitePresentation (f i)) ∧ (∀ i, Finite (M i)) ∧
        ∃ φ : F ⟶ ∐ fun i ↦ pushforwardConstantSheaf (f i) (M i), Mono φ :=
  sorry

end AbelianGroups

section Modules

variable {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
  (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable [HasCoproducts.{0} (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]

/-- A constructible étale sheaf of modules over a commutative Noetherian ring on a
quasi-compact quasi-separated scheme embeds into a finite coproduct of pushforwards of
finite-type constant module sheaves along finite finitely presented morphisms. -/
theorem IsConstructibleEtaleModule.exists_mono_to_coprod_pushforward_constantSheaf_qcqs
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)}
    (hF : IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G) F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
      (M : Fin n → ModuleCat.{w} Λ),
      (∀ i, IsFinite (f i)) ∧ (∀ i, LocallyOfFinitePresentation (f i)) ∧
        (∀ i, Module.Finite Λ (M i)) ∧
          ∃ φ : F ⟶ ∐ fun i ↦ pushforwardConstantSheaf (f i) (M i), Mono φ :=
  sorry

end Modules

end QuasiCompactQuasiSeparated

end CategoryTheory.Sheaf
