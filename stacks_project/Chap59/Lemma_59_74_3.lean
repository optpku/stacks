module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.FiniteEmbedding
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry

universe u w

/- Lemma 59.74.3 (1): the constructible set-valued embedding theorem. -/
@[stacks 09Z6] #check
  (CategoryTheory.Sheaf.IsConstructibleEtaleSet.exists_mono_to_pi_pushforward_constantSheaf :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
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
        (∀ i, IsFinite (f i)) ∧ (∀ i, Finite (E i)) ∧
            (∀ i, CategoryTheory.Sheaf.mapsOntoClosedFiniteEtaleOverOpen (f i)) ∧
              ∃ φ : F ⟶ ∏ᶜ fun i ↦
                CategoryTheory.Sheaf.pushforwardConstantSheaf (f i) (E i), Mono φ)

/- Lemma 59.74.3 (2): the constructible abelian-group-valued embedding theorem. -/
@[stacks 09Z6] #check
  (CategoryTheory.Sheaf.IsConstructibleEtaleAddCommGrp.exists_mono_to_coprod_pushforward_constantSheaf :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
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
        (∀ i, IsFinite (f i)) ∧ (∀ i, Finite (M i)) ∧
            (∀ i, CategoryTheory.Sheaf.mapsOntoClosedFiniteEtaleOverOpen (f i)) ∧
              ∃ φ : F ⟶ ∐ fun i ↦
                  CategoryTheory.Sheaf.pushforwardConstantSheaf (f i) (M i), Mono φ)

/- Lemma 59.74.3 (3): the constructible module-valued embedding theorem. -/
@[stacks 09Z6] #check
  (CategoryTheory.Sheaf.IsConstructibleEtaleModule.exists_mono_to_coprod_pushforward_constantSheaf :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
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
        (∀ i, IsFinite (f i)) ∧ (∀ i, Module.Finite Λ (M i)) ∧
            (∀ i, CategoryTheory.Sheaf.mapsOntoClosedFiniteEtaleOverOpen (f i)) ∧
              ∃ φ : F ⟶ ∐ fun i ↦
                  CategoryTheory.Sheaf.pushforwardConstantSheaf (f i) (M i), Mono φ)
