/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Precomposition
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Postcomposition
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Hom-Complex Cohomology

The canonical equivalence from Hom-complex cohomology to shifted morphisms in the homotopy
category is linear over every chosen enrichment ring and natural in both complexes.
-/

open CategoryTheory ComplexShape HomotopyCategory
open CategoryTheory.CochainComplex

noncomputable section

universe w v u

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The canonical additive equivalence from degree-`n` Hom-complex cohomology to shifted
morphisms in the homotopy category. -/
@[stacks 0A8L "Hom-complex cohomology as shifted homotopy Hom"]
noncomputable def homologyHomAddEquiv
    (N I : CochainComplex C ℤ) (n : ℤ) :
    (HomComplex N I).homology n ≃+
      ((HomotopyCategory.quotient C (up ℤ)).obj N ⟶
        (HomotopyCategory.quotient C (up ℤ)).obj (I⟦n⟧)) :=
  (homologyAddEquiv N I n).trans CohomologyClass.homAddEquiv

/-- Hom-complex cohomology with the module structure transported by the canonical shifted-Hom
equivalence.  Naming the bundled module keeps the enrichment ring explicit and avoids an
ambiguous global module instance on the unbundled cohomology type. -/
@[stacks 0CS5 "transported Hom-complex cohomology module"]
noncomputable def homologyModule (R : Type w) [Ring R] [Linear R C]
    (N I : CochainComplex C ℤ) (n : ℤ) : ModuleCat.{v} R :=
  @ModuleCat.of R _ ((HomComplex N I).homology n) _
    ((homologyHomAddEquiv N I n).module R)

/-- The canonical shifted-Hom equivalence is linear for the explicitly bundled Hom-complex
cohomology module. -/
@[stacks 0CS5 "Hom-complex cohomology as shifted Hom"]
noncomputable def homologyHomLinearEquiv (R : Type w) [Ring R] [Linear R C]
    (N I : CochainComplex C ℤ) (n : ℤ) :
    (homologyModule R N I n : Type v) ≃ₗ[R]
      ((HomotopyCategory.quotient C (up ℤ)).obj N ⟶
        (HomotopyCategory.quotient C (up ℤ)).obj (I⟦n⟧)) :=
  (homologyHomAddEquiv N I n).linearEquiv R

/-- The canonical additive equivalence from Hom-complex cohomology to shifted homotopy
morphisms commutes with precomposition. -/
theorem homologyHomEquiv_naturality_left
    {N N' I : CochainComplex C ℤ} (f : N ⟶ N') (n : ℤ) :
    CommSq
      (HomologicalComplex.homologyMap (homComplexPrecomp f) n)
      ((homologyHomAddEquiv N' I n).toAddCommGrpIso.hom)
      ((homologyHomAddEquiv N I n).toAddCommGrpIso.hom)
      ((preadditiveCoyoneda.map
        (((HomotopyCategory.quotient C (up ℤ)).map f).op)).app
          ((HomotopyCategory.quotient C (up ℤ)).obj (I⟦n⟧))) := sorry

/-- The linear shifted-Hom equivalence is contravariantly natural in the source complex. -/
theorem homologyHomLinearEquiv_naturality_left
    (R : Type w) [Ring R] [Linear R C]
    {N N' I : CochainComplex C ℤ} (f : N ⟶ N') (n : ℤ)
    (x : (HomComplex N' I).homology n) :
    homologyHomLinearEquiv R N I n
        (HomologicalComplex.homologyMap (homComplexPrecomp (f := f) (I := I)) n x) =
      (HomotopyCategory.quotient C (up ℤ)).map f ≫
        homologyHomLinearEquiv R N' I n x := sorry

/-- The linear shifted-Hom equivalence is covariantly natural in the target complex. -/
theorem homologyHomLinearEquiv_naturality_right
    (R : Type w) [Ring R] [Linear R C]
    {N I I' : CochainComplex C ℤ} (f : I ⟶ I') (n : ℤ)
    (x : (HomComplex N I).homology n) :
    homologyHomLinearEquiv R N I' n
        (HomologicalComplex.homologyMap (homComplexPostcomp (N := N) f) n x) =
      homologyHomLinearEquiv R N I n x ≫
        (HomotopyCategory.quotient C (up ℤ)).map (f⟦n⟧') := sorry

end CochainComplex.HomComplex
