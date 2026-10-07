module

public import stacks_project.Chap92.Lemma_92_23_1_IsoClass
public import stacks_project.Chap92.Lemma_92_23_1_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Deformations of ringed topoi and the cotangent complex

In the first-order thickening situation of 92.23.0.1, solutions are governed by
Ext⁽n⁾_O(L[f], G): a canonical class ξ in Ext⁽2⁾ vanishes iff a solution exists;
isomorphism classes of solutions are principal homogeneous under Ext⁽1⁾;
automorphisms of a given solution fitting the diagram are Ext⁽0⁾.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits DerivedCategory
open CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open RingedSite.FirstOrderThickening
open scoped DerivedExt RingedSite.ToposHom SheafOfModules.RingedSite

namespace RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC.HasSheafCompose (forget RingCat.{u})]
variable [JD.HasSheafCompose (forget RingCat.{u})]
variable [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [JD.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [JC.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [JD.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JD CommRingCat.{u}]
variable [JC.WEqualsLocallyBijective CommRingCat.{u}]
variable [JD.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [UnivLE.{u, u}]

-- Local instance justification (defeq pin): moduleCategoryHasDerivedCategory is the reducible
-- standard HasDerivedCategory owner used by 92.22.3 and 91.13.*; Ext, Q, and singleFunctor must
-- share that instance.
attribute [local instance] moduleCategoryHasDerivedCategory

variable {O : Sheaf JC CommRingCat.{u}}
variable {OB OB' : Sheaf JD CommRingCat.{u}}
variable (t : OB' ⟶ OB) [IsFirstOrderThickening t]
variable (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
variable (G : SheafOfModules.{u} (ringSheaf JC O))
variable (c : inverseImageIdeal f t ⟶ (SheafOfModules.restrictScalars f.structureMap).obj G)

/-- Lemma 92.23.1 (1) In the situation above we have: there is a canonical element
ξ ∈ Ext⁽2⁾_O(L[f], G) whose vanishing is a sufficient and necessary condition for the
existence of a solution to (92.23.0.1). -/
@[stacks 08V5]
theorem existenceObstruction_eq_zero_iff :
    existenceObstruction t f G c = 0 ↔ Nonempty (Solution t f G c) :=
  sorry

/-- Lemma 92.23.1 (2) If there exists a solution, then the set of isomorphism classes of
solutions is principal homogeneous under Ext⁽1⁾_O(L[f], G). Existence is the basepoint S0;
the acting group is Ext⁽1⁾ of Q L[f] with coefficients Q(G[0]), identified with Ext⁽1⁾ of
Q NL[f] by NL[f] = τ_{≥ -1} L[f]. -/
@[stacks 08V5]
def isoClassDerivedEquiv (S0 : Solution t f G c) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj L[f], coeffSingle G) ≃ IsoClass t f G c :=
  (extOneTruncEquiv f G).symm.trans (isoClassNaiveEquiv t f G c S0)

/-- The based chart sends a derived Ext¹ class to the translate of the basepoint. -/
theorem isoClassDerivedEquiv_apply (S0 : Solution t f G c)
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj L[f], coeffSingle G)) :
    isoClassDerivedEquiv t f G c S0 ξ =
      isoClassNaiveEquiv t f G c S0 ((extOneTruncEquiv f G).symm ξ) :=
  sorry

/-- The zero Ext¹ class is sent to the class of the basepoint. -/
theorem isoClassDerivedEquiv_zero (S0 : Solution t f G c) :
    isoClassDerivedEquiv t f G c S0 0 = isoClassMk t f G c S0 :=
  sorry

/-- The inverse chart is the naive torsor subtraction, transported along
`extOneTruncEquiv`. -/
theorem isoClassDerivedEquiv_symm_apply (S0 : Solution t f G c)
    (p : IsoClass t f G c) :
    (isoClassDerivedEquiv t f G c S0).symm p =
      extOneTruncEquiv f G ((isoClassNaiveEquiv t f G c S0).symm p) :=
  sorry

/-- Lemma 92.23.1 (3) Given a solution X', the set of automorphisms of X' fitting into
(92.23.0.1) is canonically isomorphic to Ext⁽0⁾_O(L[f], G). The automorphism type is
SolutionIso of the identity diagram compare S S. -/
@[stacks 08V5]
def autEquiv (S : Solution t f G c) :
    Ext⁽(0 : ℤ)⁾(DerivedCategory.Q.obj L[f], coeffSingle G) ≃ SolutionIso S S where
  toFun e := SolutionIso.perturb S ((extZeroHomEquiv f G).symm e) (SolutionIso.idAuto S)
  invFun φ := extZeroHomEquiv f G (SolutionIso.diff S (SolutionIso.idAuto S) φ)
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `autEquiv` sends an Ext⁰ class to the perturbation of `idAuto`. -/
theorem autEquiv_apply (S : Solution t f G c)
    (e : Ext⁽(0 : ℤ)⁾(DerivedCategory.Q.obj L[f], coeffSingle G)) :
    autEquiv t f G c S e =
      SolutionIso.perturb S ((extZeroHomEquiv f G).symm e) (SolutionIso.idAuto S) :=
  sorry

end RingedSite.FirstOrderThickening
