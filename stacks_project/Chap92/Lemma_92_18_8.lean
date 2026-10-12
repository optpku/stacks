/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_18_8_Triangle
import Mathlib.Tactic.CrossRefAttribute

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open scoped SheafOfModules.RingedSite.CotangentComplex

@[expose] public section

universe u

variable {D : Type u} [Category.{u} D] {J : GrothendieckTopology D}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [UnivLE.{u, u}]
variable {A B C : Sheaf J CommRingCat.{u}}
variable (φ : A ⟶ B) (ψ : B ⟶ C)

-- Local instance justification (defeq pin): `moduleCategoryHasDerivedCategory` is the reducible standard owner for ringed-site modules; `DerivedCategory.Q` and `distTriang` need that same instance without registering a second derived-category owner.
attribute [local instance] moduleCategoryHasDerivedCategory

namespace SheafOfModules.RingedSite.CotangentComplex

/-- Lemma 92.18.8. Let `D` be a site. Let `A ⟶ B ⟶ C` be homomorphisms of sheaves of
rings on `D`. There is a canonical distinguished triangle
`tensor φ ψ ⟶ DerivedCategory.Q.obj L(φ ≫ ψ) ⟶ DerivedCategory.Q.obj L(ψ) ⟶
(tensor φ ψ)⟦1⟧` in `D(C)`. -/
@[stacks 08SZ]
theorem transitivityTriangle_distinguished :
    transitivityTriangle φ ψ ∈
      distTriang (DerivedCategory (SheafOfModules (ringSheaf J C))) :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex
