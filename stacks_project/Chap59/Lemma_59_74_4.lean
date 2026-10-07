module

public import stacks_project.Chap59.Definition_59_71_1
public import stacks_project.Chap59.Lemma_59_74_3
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.QuasiSeparated

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u w v₁

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

section SetValued

variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
variable [HasProducts.{0} (Sheaf X.smallEtaleTopology (Type (u + 1)))]

/-- Lemma 59.74.4 (1): a constructible sheaf of sets on the small étale site of a
quasi-compact quasi-separated scheme injects into a finite product of pushforwards of
constant sheaves of finite sets along finite finitely presented morphisms. -/
@[stacks 09Z7]
theorem IsConstructibleEtaleSet.exists_mono_to_pi_pushforward_constantSheaf_qcqs
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (Type (u + 1)) →
        Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (Type (u + 1)) → Prop)
    {F : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (hF : IsConstructibleEtaleSet restrict finiteLocallyConstant F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X) (E : Fin n → Type (u + 1)),
      (∀ i, IsFinite (f i)) ∧ (∀ i, LocallyOfFinitePresentation (f i)) ∧ (∀ i, Finite (E i)) ∧
        ∃ φ : F ⟶ ∏ᶜ fun i ↦ pushforwardConstantSheaf (f i) (E i), Mono φ :=
  sorry

end SetValued

section AbelianGroups

variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasCoproducts.{0} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Lemma 59.74.4 (2): a constructible abelian sheaf on the small étale site of a
quasi-compact quasi-separated scheme injects into a finite coproduct of pushforwards of
constant sheaves of finite abelian groups along finite finitely presented morphisms. -/
@[stacks 09Z7]
theorem IsConstructibleEtaleAddCommGrp.exists_mono_to_coprod_pushforward_constantSheaf_qcqs
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} →
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleEtaleAddCommGrp restrict finiteLocallyConstant F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
      (M : Fin n → Type (u + 1)) (inst : ∀ i, AddCommGroup (M i)),
      (∀ i, IsFinite (f i)) ∧ (∀ i, LocallyOfFinitePresentation (f i)) ∧ (∀ i, Finite (M i)) ∧
        ∃ φ : F ⟶ ∐ fun i ↦ pushforwardConstantSheaf (f i) (AddCommGrpCat.of (M i)),
          Mono φ :=
  sorry

end AbelianGroups

section Modules

variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [HasCoproducts.{0} (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]

/-- Lemma 59.74.4 (3): for a Noetherian ring `Λ`, a constructible sheaf of `Λ`-modules on the
small étale site of a quasi-compact quasi-separated scheme injects into a finite coproduct of
pushforwards of constant sheaves of finite `Λ`-modules along finite finitely presented
morphisms. -/
@[stacks 09Z7]
theorem IsConstructibleEtaleModule.exists_mono_to_coprod_pushforward_constantSheaf_qcqs
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ) →
        Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ) → Prop)
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)}
    (hF : IsConstructibleEtaleModule restrict finiteTypeLocallyConstant F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X) (M : Fin n → ModuleCat.{w} Λ),
      (∀ i, IsFinite (f i)) ∧ (∀ i, LocallyOfFinitePresentation (f i)) ∧
          (∀ i, Module.Finite Λ (M i)) ∧
        ∃ φ : F ⟶ ∐ fun i ↦ pushforwardConstantSheaf (f i) (M i), Mono φ :=
  sorry

end Modules

end CategoryTheory.Sheaf
