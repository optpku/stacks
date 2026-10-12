/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_22_3_Triangle
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transitivity triangle of morphisms of ringed topoi

Lemma 92.22.3 records that the canonical triangle
`Lf^* L[g] ⟶ L[g ∘ f] ⟶ L[f] ⟶ (Lf^* L[g])⟦1⟧` is distinguished in `D(O1)`.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open SheafOfModules.RingedSite
open scoped RingedSite.ToposHom
open scoped SheafOfModules.RingedSite.CotangentComplex

@[expose] public section

universe u

variable {C1 C2 C3 : Type u} [Category.{u} C1] [Category.{u} C2] [Category.{u} C3]
variable {JC1 : GrothendieckTopology C1} {JC2 : GrothendieckTopology C2}
variable {JC3 : GrothendieckTopology C3}
variable [JC1.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC2.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC3.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC1.HasSheafCompose (forget RingCat.{u})]
variable [JC2.HasSheafCompose (forget RingCat.{u})]
variable [JC3.HasSheafCompose (forget RingCat.{u})]
variable [JC1.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [JC2.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify JC1 CommRingCat.{u}]
variable [HasWeakSheafify JC2 CommRingCat.{u}]
variable [HasWeakSheafify JC1 AddCommGrpCat.{u}]
variable [HasWeakSheafify JC2 AddCommGrpCat.{u}]
variable [JC1.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JC2.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [UnivLE.{u, u}]
variable {OC1 : Sheaf JC1 CommRingCat.{u}} {OC2 : Sheaf JC2 CommRingCat.{u}}
variable {OC3 : Sheaf JC3 CommRingCat.{u}}
variable (f : RingedSite.ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
  (RingedSite.ofCommRingSheaf JC2 OC2))
variable (g : RingedSite.ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
  (RingedSite.ofCommRingSheaf JC3 OC3))

-- Local instance justification (defeq pin): `moduleCategoryHasDerivedCategory` is the reducible standard owner for ringed-site modules; `DerivedCategory.Q` and `distTriang` need that same instance without registering a second derived-category owner.
attribute [local instance] moduleCategoryHasDerivedCategory

namespace RingedSite.ToposHom

/-- Lemma 92.22.3. Let `f : (Sh(C1), O1) ⟶ (Sh(C2), O2)` and
`g : (Sh(C2), O2) ⟶ (Sh(C3), O3)` be morphisms of ringed topoi. Then there is a
canonical distinguished triangle
`pullbackCotangent f g ⟶ DerivedCategory.Q.obj L[comp f g] ⟶
DerivedCategory.Q.obj L[f] ⟶ (pullbackCotangent f g)⟦1⟧` in `D(O1)`. -/
@[stacks 08V1]
theorem transitivityTriangle_distinguished :
    transitivityTriangle f g ∈
      distTriang (DerivedCategory (SheafOfModules (ringSheaf JC1 OC1))) :=
  sorry

end RingedSite.ToposHom
