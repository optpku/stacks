module

public import stacks_project.Chap59.Definition_59_71_1
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Subobject.NoetherianObject

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} [IsNoetherian X]

section SetValued

variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]

/-- Lemma 59.74.2 (1): on a Noetherian scheme, a constructible sheaf of sets on `Xₑₜ` is a
Noetherian object, so an ascending chain of subsheaves contained in it eventually stabilizes. -/
@[stacks 09YV]
theorem IsConstructibleEtaleSet.isNoetherianObject
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (Type (u + 1)) →
        Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (Type (u + 1)) → Prop)
    {F : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (hF : IsConstructibleEtaleSet restrict finiteLocallyConstant F) :
    IsNoetherianObject F := sorry

/-- An ascending chain `F₁ ⊂ F₂ ⊂ ⋯ ⊂ F` of sheaves of sets on `Xₑₜ` contained in a constructible
sheaf `F` eventually equals its later terms as subobjects of `F`. -/
theorem IsConstructibleEtaleSet.stabilizes_subobject_chain
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (Type (u + 1)) →
        Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (Type (u + 1)) → Prop)
    {F : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (hF : IsConstructibleEtaleSet restrict finiteLocallyConstant F)
    (f : ℕ →o Subobject F) :
    ∃ n, ∀ m, n ≤ m → f n = f m := sorry

end SetValued

section AbelianGroups

variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
variable [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Lemma 59.74.2 (2): on a Noetherian scheme, a constructible sheaf of abelian groups on `Xₑₜ` is
a Noetherian object, so an ascending chain of subsheaves contained in it eventually stabilizes. -/
@[stacks 09YV]
theorem IsConstructibleEtaleAddCommGrp.isNoetherianObject
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} →
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleEtaleAddCommGrp restrict finiteLocallyConstant F) :
    IsNoetherianObject F := sorry

/-- An ascending chain `F₁ ⊂ F₂ ⊂ ⋯ ⊂ F` of abelian sheaves on `Xₑₜ` contained in a constructible
sheaf `F` eventually equals its later terms as subobjects of `F`. -/
theorem IsConstructibleEtaleAddCommGrp.stabilizes_subobject_chain
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} →
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleEtaleAddCommGrp restrict finiteLocallyConstant F)
    (f : ℕ →o Subobject F) :
    ∃ n, ∀ m, n ≤ m → f n = f m := sorry

end AbelianGroups

section Modules

variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]

/-- Lemma 59.74.2 (3): on a Noetherian scheme, for a Noetherian ring `Λ`, a constructible sheaf of
`Λ`-modules on `Xₑₜ` is a Noetherian object, so an ascending chain of subsheaves contained in it
eventually stabilizes. -/
@[stacks 09YV]
theorem IsConstructibleEtaleModule.isNoetherianObject
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ) →
        Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ) → Prop)
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)}
    (hF : IsConstructibleEtaleModule restrict finiteTypeLocallyConstant F) :
    IsNoetherianObject F := sorry

/-- An ascending chain `F₁ ⊂ F₂ ⊂ ⋯ ⊂ F` of sheaves of `Λ`-modules on `Xₑₜ` contained in a
constructible sheaf `F` eventually equals its later terms as subobjects of `F`. -/
theorem IsConstructibleEtaleModule.stabilizes_subobject_chain
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ) →
        Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ) → Prop)
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)}
    (hF : IsConstructibleEtaleModule restrict finiteTypeLocallyConstant F)
    (f : ℕ →o Subobject F) :
    ∃ n, ∀ m, n ≤ m → f n = f m := sorry

end Modules

end CategoryTheory.Sheaf
