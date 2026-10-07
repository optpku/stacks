module

public import stacks_project.Chap59.Definition_59_71_1
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v w v₁

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} [IsNoetherian X]

/-- Small-étale pushforward of a constant sheaf `underline{E}` along `f : Y ⟶ X`. -/
noncomputable abbrev pushforwardConstantSheaf {Y : Scheme.{u}} (f : Y ⟶ X) {D : Type v}
    [Category.{v₁} D] [HasWeakSheafify X.smallEtaleTopology D]
    [HasWeakSheafify Y.smallEtaleTopology D] (E : D) :
    Sheaf X.smallEtaleTopology D :=
  ((Scheme.smallEtalePullback f).sheafPushforwardContinuous D X.smallEtaleTopology
      Y.smallEtaleTopology).obj
    ((constantSheaf Y.smallEtaleTopology D).obj E)

/-- Unfolding of `pushforwardConstantSheaf`. -/
theorem pushforwardConstantSheaf_obj {Y : Scheme.{u}} (f : Y ⟶ X) {D : Type v}
    [Category.{v₁} D] [HasWeakSheafify X.smallEtaleTopology D]
    [HasWeakSheafify Y.smallEtaleTopology D] (E : D) :
    pushforwardConstantSheaf f E =
      ((Scheme.smallEtalePullback f).sheafPushforwardContinuous D X.smallEtaleTopology
          Y.smallEtaleTopology).obj
        ((constantSheaf Y.smallEtaleTopology D).obj E) := sorry

/-- Geometric moreover of Lemma 59.74.3: `Y` is irreducible and reduced, and `f` factors as a
surjection onto an irreducible reduced closed subscheme `Z ⊆ X` that is finite étale over a
nonempty open of `Z`. -/
def mapsOntoClosedFiniteEtaleOverOpen {Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  IrreducibleSpace Y ∧ IsReduced Y ∧
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (g : Y ⟶ Z),
      IsClosedImmersion i ∧ f = g ≫ i ∧ IrreducibleSpace Z ∧ IsReduced Z ∧
        Function.Surjective g.base ∧
          ∃ (U : Z.Opens), Nonempty U ∧
            Etale (pullback.fst (U.ι) g) ∧ IsFinite (pullback.fst (U.ι) g)

/-- Unpacking of `mapsOntoClosedFiniteEtaleOverOpen`. -/
theorem mapsOntoClosedFiniteEtaleOverOpen_iff {Y : Scheme.{u}} (f : Y ⟶ X) :
    mapsOntoClosedFiniteEtaleOverOpen f ↔
      IrreducibleSpace Y ∧ IsReduced Y ∧
        ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (g : Y ⟶ Z),
          IsClosedImmersion i ∧ f = g ≫ i ∧ IrreducibleSpace Z ∧ IsReduced Z ∧
            Function.Surjective g.base ∧
              ∃ (U : Z.Opens), Nonempty U ∧
                Etale (pullback.fst (U.ι) g) ∧ IsFinite (pullback.fst (U.ι) g) :=
  sorry

section SetValued

variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
variable [HasProducts.{0} (Sheaf X.smallEtaleTopology (Type (u + 1)))]

/-- Lemma 59.74.3 (1): a constructible sheaf of sets on the small étale site of a Noetherian
scheme injects into a finite product of pushforwards of constant sheaves of finite sets along
finite morphisms, and the finite models may be taken irreducible and reduced, mapping onto an
irreducible reduced closed subscheme over which they are finite étale on a nonempty open. -/
@[stacks 09Z6]
theorem IsConstructibleEtaleSet.exists_mono_to_pi_pushforward_constantSheaf
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (Type (u + 1)) →
        Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (Type (u + 1)) → Prop)
    {F : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (hF : IsConstructibleEtaleSet restrict finiteLocallyConstant F) :
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

/-- Lemma 59.74.3 (2): a constructible abelian sheaf on the small étale site of a Noetherian
scheme injects into a finite coproduct of pushforwards of constant sheaves of finite abelian
groups along finite morphisms, with the same geometric constraints on the finite models. -/
@[stacks 09Z6]
theorem IsConstructibleEtaleAddCommGrp.exists_mono_to_coprod_pushforward_constantSheaf
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} →
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleEtaleAddCommGrp restrict finiteLocallyConstant F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
      (M : Fin n → Type (u + 1)) (inst : ∀ i, AddCommGroup (M i)),
      (∀ i, IsFinite (f i)) ∧ (∀ i, Finite (M i)) ∧
          (∀ i, mapsOntoClosedFiniteEtaleOverOpen (f i)) ∧
            ∃ φ : F ⟶ ∐ fun i ↦
                pushforwardConstantSheaf (f i) (AddCommGrpCat.of (M i)),
              Mono φ :=
  sorry

end AbelianGroups

section Modules

variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [HasCoproducts.{0} (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]

/-- Lemma 59.74.3 (3): for a Noetherian ring `Λ`, a constructible sheaf of `Λ`-modules on the
small étale site of a Noetherian scheme injects into a finite coproduct of pushforwards of
constant sheaves of finite `Λ`-modules along finite morphisms, with the same geometric
constraints on the finite models. -/
@[stacks 09Z6]
theorem IsConstructibleEtaleModule.exists_mono_to_coprod_pushforward_constantSheaf
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ) →
        Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ) → Prop)
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)}
    (hF : IsConstructibleEtaleModule restrict finiteTypeLocallyConstant F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ X) (M : Fin n → ModuleCat.{w} Λ),
      (∀ i, IsFinite (f i)) ∧ (∀ i, Module.Finite Λ (M i)) ∧
          (∀ i, mapsOntoClosedFiniteEtaleOverOpen (f i)) ∧
            ∃ φ : F ⟶ ∐ fun i ↦ pushforwardConstantSheaf (f i) (M i), Mono φ :=
  sorry

end Modules

end CategoryTheory.Sheaf
