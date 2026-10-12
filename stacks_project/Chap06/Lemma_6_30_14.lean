/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Basis.Algebraic.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits TopCat TopologicalSpace

noncomputable section

universe w v u u1

section

variable {C : Type u} [Category.{v} C]
variable {F : C ⥤ Type u1} [IsAlgebraicStructure C F]
variable [HasLimitsOfSize.{w, w} C] [PreservesLimitsOfSize.{w, w} F]
variable {X Y : TopCat.{w}} (f : X ⟶ Y)
variable {ℱ : X.Sheaf C} {𝒢 : Y.Sheaf C}
variable {B : Set (Opens Y)} (hB : Opens.IsBasis B)

/-
The source's compatible maps on basis opens are exactly a morphism between the restrictions of
`𝒢` and `f_* ℱ` under `AlgebraicBasisSheaf.restriction (F := F) hB`. Lemma 6.30.10 makes
this restriction
functor an equivalence, so fullness gives the extension and faithfulness gives its uniqueness.
Keeping the basis morphism as the input preserves compatibility with restriction maps without
introducing a second family structure or a parallel dense-subsite owner.
-/
/- Lemma 6.30.14: a compatible morphism on the basis `B` from `𝒢` to the restriction of
`f_* ℱ` extends uniquely to an `f`-map `𝒢 ⟶ f_* ℱ`. -/
@[stacks 009V]
#check
  AlgebraicBasisSheaf.existsUnique_pushforwardHom_of_restriction
    (G := F) f hB

end
