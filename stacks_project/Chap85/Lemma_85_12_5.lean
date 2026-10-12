/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_12_5_Descent
public import stacks_project.Chap85.Lemma_85_12_5_Equivalence

/-!
# Lemma 85.12.5

In Situation 85.3.3, cartesian `O`-modules on `C_total` are equivalent to pairs
`(F, α)` consisting of an `O_0`-module and an isomorphism
`α : (f_{δ 1})^* F ≅ (f_{δ 0})^* F` of `O_1`-modules satisfying the `O_2` cocycle.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial
open CategoryTheory.SimplicialSites
open CategoryTheory.SimplicialSites.Module
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

/-- Lemma 85.12.5
In Situation 85.3.3 let `O` be a sheaf of rings on `C_total`. The category of cartesian
`O`-modules is equivalent to the category of pairs `(F, α)` where `F` is an `O_0`-module
and `α : (f_{δ 1})^* F ⟶ (f_{δ 0})^* F` is an isomorphism of `O_1`-modules such that
`(f_{δ 1})^* α = (f_{δ 0})^* α ∘ (f_{δ 2})^* α` as `O_2`-module maps. -/
@[stacks 07TH]
def moduleCartesianEquivalence : Cartesian C J O ≌ FaceDescent C J O :=
  cartesianEquivalence C J O

/-- The forward functor of `moduleCartesianEquivalence` extracts the pair `(F_0, α)`. -/
theorem moduleCartesianEquivalence_functor :
    (moduleCartesianEquivalence C J O).functor = toDescentFunctor C J O :=
  sorry

/-- The inverse functor of `moduleCartesianEquivalence` assembles a cartesian `O`-module
from a pair `(F, α)`. -/
theorem moduleCartesianEquivalence_inverse :
    (moduleCartesianEquivalence C J O).inverse = ofDescentFunctor C J O :=
  sorry

end CategoryTheory.SimplicialSites
