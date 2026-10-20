module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.Algebra.Category.DifferentialGraded.Endomorphism
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Forget
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy

/-!
# Shifted morphisms and the homology of internal Hom

For right modules over a cochain DGA, morphisms into a shift are cycles of the enriched Hom
complex, and morphisms in the DG homotopy category are its homology classes.  This is the
reusable enriched-category layer behind regular-module and Pontryagin-dual representability.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.Homotopy

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- The enriched Hom complex has homology in every degree. -/
instance homComplexHasHomology
    (M N : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (DifferentialGradedCategory.homComplex M N).HasHomology k := sorry

/-- Closed homogeneous maps are the concrete kernel of the enriched Hom differential. -/
def closedKernelEquiv (M N : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    ClosedGradedHom A M N k ≃
      (((DifferentialGradedCategory.homComplex M N).sc k).moduleCatLeftHomologyData.K :
        Type v) where
  toFun f := ⟨f.1, sorry⟩
  invFun f := ⟨f.1, sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- Closed degree-`k` maps are canonically the degree-`k` cycles of the enriched Hom complex. -/
def closedEquivCycles (M N : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    ClosedGradedHom A M N k ≃
      (DifferentialGradedCategory.homComplex M N).cycles k :=
  (closedKernelEquiv M N k).trans
    ((DifferentialGradedCategory.homComplex M N).sc k).moduleCatCyclesIso.symm.toLinearEquiv.toEquiv

/-- Ordinary DG-module morphisms `M ⟶ N[k]` are the degree-`k` cycles of the enriched Hom
complex. -/
@[stacks 09K4 "shifted DG morphisms as cycles of internal Hom"]
def shiftHomEquivCycles (M N : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (M ⟶ N[k]) ≃ (DifferentialGradedCategory.homComplex M N).cycles k :=
  (closedGradedHomEquivShiftHom A M N k).symm.trans (closedEquivCycles M N k)

/-- The shifted-Hom-to-cycles equivalence preserves the canonical `R`-module structures. -/
theorem shiftHomEquivCycles_isLinearMap
    (M N : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    IsLinearMap R (shiftHomEquivCycles M N k) := sorry

/-- Ordinary DG-module morphisms into a shift are canonically `R`-linearly equivalent to cycles
of the enriched Hom complex. -/
@[stacks 09K4 "linear shifted DG morphisms as cycles of internal Hom"]
noncomputable def shiftHomLinearEquivCycles
    (M N : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (M ⟶ N[k]) ≃ₗ[R] (DifferentialGradedCategory.homComplex M N).cycles k :=
  (shiftHomEquivCycles M N k).toLinearEquiv
    (shiftHomEquivCycles_isLinearMap M N k)

/-- The linear shifted-Hom equivalence has the same underlying map as the cycles equivalence. -/
@[simp]
theorem shiftHomLinearEquivCycles_apply
    (M N : DifferentialGradedModule.{u, v} A) (k : ℤ) (f : M ⟶ N[k]) :
    shiftHomLinearEquivCycles M N k f = shiftHomEquivCycles M N k f := sorry

/-- A represented homotopy class maps to the homology class of its corresponding Hom cycle. -/
def homotopyToHomology (M N : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    ((toK A).obj M ⟶ (toK A).obj N[k]) →
      (DifferentialGradedCategory.homComplex M N).homology k :=
  Quotient.lift
    (fun f ↦ ModuleCat.Hom.hom
      ((DifferentialGradedCategory.homComplex M N).homologyπ k)
      (shiftHomEquivCycles M N k (compHomToHom f))) sorry

/-- Choose a cycle representative through ModuleCat's explicit kernel-quotient homology model. -/
def cycleOfHomology (M N : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (x : (DifferentialGradedCategory.homComplex M N).homology k) :
    (DifferentialGradedCategory.homComplex M N).cycles k :=
  ((DifferentialGradedCategory.homComplex M N).sc k).moduleCatCyclesIso.inv
    (Quotient.out
      (((DifferentialGradedCategory.homComplex M N).sc k).moduleCatHomologyIso.hom x))

/-- The chosen cycle representative projects to the original Hom-complex homology class. -/
@[simp]
theorem cycleOfHomology_homologyπ (M N : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (x : (DifferentialGradedCategory.homComplex M N).homology k) :
    ModuleCat.Hom.hom ((DifferentialGradedCategory.homComplex M N).homologyπ k)
      (cycleOfHomology M N k x) = x := sorry

/-- A Hom-complex homology class determines its morphism in the DG homotopy category. -/
def homotopyOfHomology (M N : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (x : (DifferentialGradedCategory.homComplex M N).homology k) :
    (toK A).obj M ⟶ (toK A).obj N[k] :=
  (toK A).map ((shiftHomEquivCycles M N k).symm (cycleOfHomology M N k x))

/-- Morphisms `M ⟶ N[k]` in the DG homotopy category are canonically the degree-`k` homology
classes of the enriched Hom complex. -/
@[stacks 09K4 "shifted homotopy morphisms as homology of internal Hom"]
def shiftHomotopyEquivHomology (M N : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    ((toK A).obj M ⟶ (toK A).obj N[k]) ≃
      (DifferentialGradedCategory.homComplex M N).homology k where
  toFun := homotopyToHomology M N k
  invFun := homotopyOfHomology M N k
  left_inv := sorry
  right_inv := sorry

/-- The homotopy-to-homology equivalence is induced from the cycles equivalence. -/
@[simp]
theorem shiftHomotopyEquivHomology_apply
    (M N : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f : (toK A).obj M ⟶ (toK A).obj N[k]) :
    shiftHomotopyEquivHomology M N k f = homotopyToHomology M N k f := sorry

/-- The homotopy-to-Hom-complex-homology equivalence preserves the canonical `R`-module
structures. -/
theorem shiftHomotopyEquivHomology_isLinearMap
    (M N : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    IsLinearMap R (shiftHomotopyEquivHomology M N k) := sorry

/-- Shifted morphisms in the DG homotopy category are canonically `R`-linearly equivalent to
the corresponding homology of the enriched Hom complex. -/
@[stacks 09K4 "linear shifted homotopy morphisms as homology of internal Hom"]
noncomputable def shiftHomotopyLinearEquivHomology
    (M N : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    ((toK A).obj M ⟶ (toK A).obj N[k]) ≃ₗ[R]
      (DifferentialGradedCategory.homComplex M N).homology k :=
  (shiftHomotopyEquivHomology M N k).toLinearEquiv
    (shiftHomotopyEquivHomology_isLinearMap M N k)

/-- The linear shifted-Hom equivalence has the same underlying map as the canonical
homotopy-to-homology equivalence. -/
@[simp]
theorem shiftHomotopyLinearEquivHomology_apply
    (M N : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f : (toK A).obj M ⟶ (toK A).obj N[k]) :
    shiftHomotopyLinearEquivHomology M N k f =
      shiftHomotopyEquivHomology M N k f := sorry

end DifferentialGradedModule.Homotopy
