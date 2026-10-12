/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.ExtensionByZero
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u w

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}} (j : U ⟶ X)
variable [CompactSpace U] [QuasiSeparatedSpace U]
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [Etale j]

variable [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) (Type (u + 1))]

/- Lemma 59.73.1 (1): for an étale morphism `j : U ⟶ X` of quasi-compact quasi-separated
schemes, the sheafified representable `h_U` is a constructible sheaf of sets on `Xₑₜ`. -/
@[stacks 03S8] #check
  (AlgebraicGeometry.Scheme.sheafifiedRepresentable_isConstructibleEtaleSet j :
    CategoryTheory.Sheaf.IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstant G)
      (X.smallEtaleTopology.sheafifiedRepresentable
        (MorphismProperty.Over.mk ⊤ j inferInstance)))

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasWeakSheafify U.smallEtaleTopology AddCommGrpCat.{u + 1}]

/- Lemma 59.73.1 (2): for an étale morphism `j : U ⟶ X` of quasi-compact quasi-separated
schemes and a finite abelian group `M`, the extension by zero `j_! underline(M)` is a
constructible abelian sheaf on `Xₑₜ`. -/
@[stacks 03S8] #check
  (AlgebraicGeometry.Scheme.abelianExtensionByZero_constant_isConstructibleEtaleAddCommGrp j :
    CategoryTheory.Sheaf.IsConstructibleEtaleAddCommGrp
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstantAddCommGrp G)
      ((abelianExtensionByZero j).obj
        ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (.of M))))

variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable {M : Type w} [AddCommGroup M] [Module Λ M] [Module.Finite Λ M]
variable [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [HasWeakSheafify U.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{w} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
  (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/- Lemma 59.73.1 (3): for an étale morphism `j : U ⟶ X` of quasi-compact quasi-separated
schemes, a Noetherian ring `Λ`, and a finite `Λ`-module `M`, the extension by zero
`j_! underline(M)` is a constructible sheaf of `Λ`-modules on `Xₑₜ`. -/
@[stacks 03S8] #check
  (AlgebraicGeometry.Scheme.moduleExtensionByZero_constant_isConstructibleEtaleModule j :
    CategoryTheory.Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((moduleExtensionByZero j).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{w} Λ)).obj
          (.of Λ M))))

end AlgebraicGeometry.Scheme
