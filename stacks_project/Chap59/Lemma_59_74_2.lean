module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Noetherian
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

variable (X : Scheme.{u}) [IsNoetherian X]

section SetValued

variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]

/- Lemma 59.74.2 (1): on a Noetherian scheme, an ascending chain of subsheaves of a
constructible sheaf of sets on `Xₑₜ` eventually stabilizes. -/
@[stacks 09YV]
#check (CategoryTheory.Sheaf.IsConstructibleEtaleSet.stabilizes_subobject_chain (X := X) :
    ∀ {F : Sheaf X.smallEtaleTopology (Type (u + 1))},
      IsConstructibleEtaleSet
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstant G) F →
      ∀ f : ℕ →o Subobject F, ∃ n, ∀ m, n ≤ m → f n = f m)

end SetValued

section AbelianGroups

variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
variable [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/- Lemma 59.74.2 (2): on a Noetherian scheme, an ascending chain of subsheaves of a
constructible sheaf of abelian groups on `Xₑₜ` eventually stabilizes. -/
@[stacks 09YV]
#check (CategoryTheory.Sheaf.IsConstructibleEtaleAddCommGrp.stabilizes_subobject_chain (X := X) :
    ∀ {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}},
      IsConstructibleEtaleAddCommGrp
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F →
      ∀ f : ℕ →o Subobject F, ∃ n, ∀ m, n ≤ m → f n = f m)

end AbelianGroups

section Modules

variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]
variable [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/- Lemma 59.74.2 (3): on a Noetherian scheme, an ascending chain of subsheaves of a
constructible sheaf of `Λ`-modules on `Xₑₜ` eventually stabilizes. -/
@[stacks 09YV]
#check (CategoryTheory.Sheaf.IsConstructibleEtaleModule.stabilizes_subobject_chain (X := X) (Λ := Λ) :
    ∀ {F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)},
      IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
          IsFiniteTypeLocallyConstantModule G) F →
      ∀ f : ℕ →o Subobject F, ∃ n, ∀ m, n ≤ m → f n = f m)

end Modules

end CategoryTheory.Sheaf
