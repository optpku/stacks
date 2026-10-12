/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Remark_92_18_5_Sections
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical maps from objectwise cotangent complexes

Remark 92.18.5 records the canonical map of complexes of `B(U)`-modules
`L(B(U)/A(U)) ⟶ L(φ)(U)`, its compatibility with restriction, and the
identification of `L(φ)` with the sheafification of `U ↦ L(B(U)/A(U))`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open Opposite
open SheafOfModules.RingedSite.CotangentComplex
open SheafOfModules.RingedSite.CotangentComplex.Homology
open scoped SheafOfModules.RingedSite.CotangentComplex

noncomputable section

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

/- Remark 92.18.5 (1). For any object `U` of the site there is a canonical map
`L(B(U)/A(U)) ⟶ L(φ)(U)` of complexes of `B(U)`-modules. -/
@[stacks 08SX]
#check @sectionsComplexMap

/-- Remark 92.18.5 (2). The canonical maps `L(B(U)/A(U)) ⟶ L(φ)(U)` are compatible
with restriction along morphisms of the site. -/
@[stacks 08SX]
theorem sectionsComplexMap_naturality {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    sectionsComplexMap φ X ≫ Sections.evalRestrict φ f =
      complexMap φ f ≫
        ((ModuleCat.restrictScalars (B.obj.map f).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (sectionsComplexMap φ Y) :=
  sorry

/-- Remark 92.18.5 (3). The complex `L(φ)` is the sheafification of the rule
`U ↦ L(B(U)/A(U))`. -/
@[stacks 08SX]
instance sheafifyIso {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    IsIso (Sections.comparison φ) :=
  sorry
