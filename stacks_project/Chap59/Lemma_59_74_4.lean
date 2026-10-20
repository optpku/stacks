module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.FiniteEmbedding
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry

universe u w

/- Lemma 59.74.4 (1): a constructible sheaf of sets on the small étale site of a
quasi-compact quasi-separated scheme injects into a finite product of pushforwards of
constant sheaves of finite sets along finite finitely presented morphisms. -/
@[stacks 09Z7] #check
  (CategoryTheory.Sheaf.IsConstructibleEtaleSet.exists_mono_to_pi_pushforward_constantSheaf_qcqs :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
      [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
      [HasProducts.{0} (Sheaf X.smallEtaleTopology (Type (u + 1)))]
      {F : Sheaf X.smallEtaleTopology (Type (u + 1))},
      IsConstructibleEtaleSet
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstant G) F →
      ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X) (E : Fin n → Type (u + 1)),
        (∀ i, IsFinite (f i)) ∧ (∀ i, LocallyOfFinitePresentation (f i)) ∧ (∀ i, Finite (E i)) ∧
          ∃ φ : F ⟶ ∏ᶜ fun i ↦ pushforwardConstantSheaf (f i) (E i), Mono φ)

/- Lemma 59.74.4 (2): a constructible abelian sheaf on the small étale site of a
quasi-compact quasi-separated scheme injects into a finite coproduct of pushforwards of
constant sheaves of finite abelian groups along finite finitely presented morphisms. -/
@[stacks 09Z7] #check
  (CategoryTheory.Sheaf.IsConstructibleEtaleAddCommGrp.exists_mono_to_coprod_pushforward_constantSheaf_qcqs :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasCoproducts.{0} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
      {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}},
      IsConstructibleEtaleAddCommGrp
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F →
      ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
        (M : Fin n → AddCommGrpCat.{u + 1}),
        (∀ i, IsFinite (f i)) ∧ (∀ i, LocallyOfFinitePresentation (f i)) ∧ (∀ i, Finite (M i)) ∧
          ∃ φ : F ⟶ ∐ fun i ↦ pushforwardConstantSheaf (f i) (M i), Mono φ)

/- Lemma 59.74.4 (3): for a Noetherian ring `Λ`, a constructible sheaf of `Λ`-modules on the
small étale site of a quasi-compact quasi-separated scheme injects into a finite coproduct of
pushforwards of constant sheaves of finite `Λ`-modules along finite finitely presented
morphisms. -/
@[stacks 09Z7] #check
  (CategoryTheory.Sheaf.IsConstructibleEtaleModule.exists_mono_to_coprod_pushforward_constantSheaf_qcqs :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
      [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
      [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
      [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
        (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
      [HasCoproducts.{0} (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]
      {F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)},
      IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G) F →
      ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
        (M : Fin n → ModuleCat.{w} Λ),
        (∀ i, IsFinite (f i)) ∧ (∀ i, LocallyOfFinitePresentation (f i)) ∧
          (∀ i, Module.Finite Λ (M i)) ∧
            ∃ φ : F ⟶ ∐ fun i ↦ pushforwardConstantSheaf (f i) (M i), Mono φ)
