/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Closure
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

variable (X : Scheme.{u}) [IsNoetherian X]

section SetValued

/- Proposition 59.74.1 (1): on a Noetherian scheme, any subsheaf of a constructible sheaf of
sets on `Xₑₜ` is constructible. -/
@[stacks 09BH]
#check
  (CategoryTheory.Sheaf.constructibleEtaleSet_isClosedUnderSubobjects (X := X) :
    IsClosedUnderSubobjects
      (fun F : Sheaf X.smallEtaleTopology (Type (u + 1)) ↦
        IsConstructibleEtaleSet
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteLocallyConstant G) F))

/- Proposition 59.74.1 (2): on a Noetherian scheme, any quotient sheaf of a constructible sheaf
of sets on `Xₑₜ` is constructible. -/
@[stacks 09BH]
#check
  (CategoryTheory.Sheaf.constructibleEtaleSet_isClosedUnderQuotients (X := X) :
    IsClosedUnderQuotients
      (fun F : Sheaf X.smallEtaleTopology (Type (u + 1)) ↦
        IsConstructibleEtaleSet
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteLocallyConstant G) F))

end SetValued

section AbelianGroups

variable [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/- Proposition 59.74.1 (3): on a Noetherian scheme, constructible abelian sheaves on `Xₑₜ`
form a strong Serre subcategory of `Ab(Xₑₜ)`, so its inherited subobject and quotient closure
give the corresponding constructibility statements. -/
@[stacks 09BH]
#check
  (CategoryTheory.Sheaf.constructibleEtaleAddCommGrp_isSerreClass (X := X) :
    IsSerreClass
      (fun F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ↦
        IsConstructibleEtaleAddCommGrp
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F))

end AbelianGroups

section Modules

variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]
variable [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/- Proposition 59.74.1 (4): on a Noetherian scheme, for a Noetherian ring `Λ`, constructible
sheaves of `Λ`-modules on `Xₑₜ` form a strong Serre subcategory of `Mod(Xₑₜ, Λ)`, so its inherited
subobject and quotient closure give the corresponding constructibility statements. -/
@[stacks 09BH]
#check
  (CategoryTheory.Sheaf.constructibleEtaleModule_isSerreClass (X := X) :
    IsSerreClass
      (fun F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ) ↦
        IsConstructibleEtaleModule
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
            IsFiniteTypeLocallyConstantModule G) F))

end Modules

end CategoryTheory.Sheaf
