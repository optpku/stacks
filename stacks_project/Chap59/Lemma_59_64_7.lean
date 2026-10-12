/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Monoidal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

universe u w

variable (X : Scheme.{u})
variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [((X.smallEtaleTopology.W :
  MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ))).IsMonoidal]
variable {F G : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)}
variable [Sheaf.IsLocallyConstant F] [Sheaf.IsLocallyConstant G]

/- Lemma 59.64.7: the tensor product of two locally constant sheaves of `Λ`-modules on the
small étale site of a scheme is locally constant. -/
@[stacks 095D]
#check (CategoryTheory.Sheaf.IsLocallyConstant.tensorModule (F := F) (G := G) :
  CategoryTheory.Sheaf.IsLocallyConstant (F ⊗ G))
