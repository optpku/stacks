/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf

noncomputable section

universe u v

variable {C : Type u} [Category.{u} C]
variable {K : Type v} [Category.{v} K] [Small.{u} K]
variable (J : GrothendieckTopology C) (U : C)

/- Lemma 18.3.2 (03CO) (1), limits: all small limits of abelian sheaves exist. -/
@[stacks 03CO "limits"]
#check (inferInstance : HasLimitsOfShape K (Sheaf J AddCommGrpCat.{u}))

/- Lemma 18.3.2 (03CO) (1), colimits: all small colimits of abelian sheaves exist. -/
@[stacks 03CO "colimits"]
#check (inferInstance : HasColimitsOfShape K (Sheaf J AddCommGrpCat.{u}))

/- Lemma 18.3.2 (03CO) (2): limits of abelian sheaves are created in presheaves. -/
@[stacks 03CO "limits are sectionwise"]
#check (inferInstance :
  CreatesLimitsOfShape K (sheafToPresheaf J AddCommGrpCat.{u}))

/- The corresponding sections functor preserves all small limits. -/
#check (inferInstance :
  PreservesLimitsOfShape K
    (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)))

/- Lemma 18.3.2 (03CO) (3): finite direct sums agree with the pointwise finite products. -/
@[stacks 03CO "finite direct sums"]
#check (inferInstance :
  PreservesFiniteBiproducts (sheafToPresheaf J AddCommGrpCat.{u}))

section

variable (F : K ⥤ Sheaf J AddCommGrpCat.{u})

/- Lemma 18.3.2 (03CO) (4): a colimit of sheaves is the sheafification of the presheaf
colimit. -/
@[stacks 03CO "colimits by sheafification"]
#check
  (isColimitSheafifyCocone
    (colimit.cocone (F ⋙ sheafToPresheaf J AddCommGrpCat.{u}))
    (colimit.isColimit (F ⋙ sheafToPresheaf J AddCommGrpCat.{u})))

end

/- Lemma 18.3.2 (03CO) (5): filtered colimits of abelian sheaves are exact. -/
@[stacks 03CO "filtered colimits are exact"]
#check (inferInstance : AB5 (Sheaf J AddCommGrpCat.{u}))
