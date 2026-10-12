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

universe u v w

namespace CategoryTheory.Sheaf

variable (X : Scheme.{u})

section SetValued

variable (K : Type v) [SmallCategory K] [FinCategory K]

/- Lemma 59.71.6 (1): constructible sheaves of sets on `Xₑₜ` are closed under finite limits
inside `Sh(Xₑₜ)`. -/
@[stacks 03RZ] #check
  (CategoryTheory.Sheaf.constructibleEtaleSet_isClosedUnderLimits X K :
    IsClosedUnderLimitsOfShape
      (fun F : Sheaf X.smallEtaleTopology (Type (u + 1)) ↦
        IsConstructibleEtaleSet
          (fun {Y} f =>
            ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} (G : Sheaf Y.smallEtaleTopology (Type (u + 1))) ↦
            IsFiniteLocallyConstant G) F) K)

/- Lemma 59.71.6 (2): constructible sheaves of sets on `Xₑₜ` are closed under finite colimits
inside `Sh(Xₑₜ)`. -/
@[stacks 03RZ] #check
  (CategoryTheory.Sheaf.constructibleEtaleSet_isClosedUnderColimits X K :
    IsClosedUnderColimitsOfShape
      (fun F : Sheaf X.smallEtaleTopology (Type (u + 1)) ↦
        IsConstructibleEtaleSet
          (fun {Y} f =>
            ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} (G : Sheaf Y.smallEtaleTopology (Type (u + 1))) ↦
            IsFiniteLocallyConstant G) F) K)

end SetValued

section AbelianGroups

variable [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/- Lemma 59.71.6 (3): constructible abelian sheaves on `Xₑₜ` form a weak Serre subcategory
of `Ab(Xₑₜ)`. -/
@[stacks 03RZ] #check
  (CategoryTheory.Sheaf.constructibleEtaleAddCommGrp_isWeakSerreClass X :
    IsWeakSerreClass
      (fun F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ↦
        IsConstructibleEtaleAddCommGrp
          (fun {Y} f =>
            ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ↦
            IsFiniteLocallyConstantAddCommGrp G) F))

end AbelianGroups

section Modules

variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]
variable [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/- Lemma 59.71.6 (4): for a Noetherian ring `Λ`, constructible sheaves of `Λ`-modules on
`Xₑₜ` form a weak Serre subcategory of `Mod(Xₑₜ, Λ)`. -/
@[stacks 03RZ] #check
  (CategoryTheory.Sheaf.constructibleEtaleModule_isWeakSerreClass X :
    IsWeakSerreClass
      (fun F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ) ↦
        IsConstructibleEtaleModule
          (fun {Y} f =>
            ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
            IsFiniteTypeLocallyConstantModule G) F))

end Modules

end CategoryTheory.Sheaf
