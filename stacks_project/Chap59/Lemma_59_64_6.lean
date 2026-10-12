/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite.Closure
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u v w

variable (X : Scheme.{u})

section Types

variable [HasWeakSheafify X.smallEtaleTopology (Type w)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (Type w)]
variable (K : Type v) [SmallCategory K] [FinCategory K]

/- Lemma 59.64.6 (1): finite locally constant sheaves of sets on the small étale site of `X`
are closed under limits indexed by a finite category. -/
@[stacks 03RX] #check
  (CategoryTheory.Sheaf.finiteLocallyConstant.isClosedUnderLimitsOfShape
    (J := X.smallEtaleTopology) K :
  IsClosedUnderLimitsOfShape
    (Sheaf.finiteLocallyConstant X.smallEtaleTopology) K)

/- Lemma 59.64.6 (2): finite locally constant sheaves of sets on the small étale site of `X`
are closed under colimits indexed by a finite category. -/
@[stacks 03RX] #check
  (CategoryTheory.Sheaf.finiteLocallyConstant.isClosedUnderColimitsOfShape
    (J := X.smallEtaleTopology) K :
  IsClosedUnderColimitsOfShape
    (Sheaf.finiteLocallyConstant X.smallEtaleTopology) K)

end Types

section AddCommGroups

variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{w}]
variable [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})]

/- Lemma 59.64.6 (3): finite locally constant abelian sheaves on the small étale site of `X`
form a weak Serre subcategory of all abelian sheaves. -/
@[stacks 03RX] #check
  (CategoryTheory.Sheaf.finiteLocallyConstantAddCommGrp.isWeakSerreClass
    (J := X.smallEtaleTopology) :
  IsWeakSerreClass
    (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology))

end AddCommGroups

section Modules

variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]

/- Lemma 59.64.6 (4): for a Noetherian ring `Λ`, finite-type locally constant sheaves of
`Λ`-modules on the small étale site of `X` form a weak Serre subcategory. -/
@[stacks 03RX] #check
  (CategoryTheory.Sheaf.finiteTypeLocallyConstantModule.isWeakSerreClass
    (J := X.smallEtaleTopology) (R := Λ) :
  IsWeakSerreClass
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ))

end Modules
