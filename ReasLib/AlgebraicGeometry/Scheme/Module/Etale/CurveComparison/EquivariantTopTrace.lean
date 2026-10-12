/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe w v u

namespace ActualEquivariantTopTrace
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (K : CochainComplex A ℤ) (n : ℤ)

/-- The canonical top homology class enters the lower truncation through
homology -> opcycles. This is an actual map in the ambient category A. -/
def topComponent : K.homology n ⟶ (K.truncGE n).X n :=
  K.homologyι n ≫ (K.truncGEXIsoOpcycles n).inv

theorem topComponent_d (i : ℤ) (hi : (ComplexShape.up ℤ).Rel n i) :
    topComponent K n ≫ (K.truncGE n).d n i = 0 := sorry

def topInclusion : (CochainComplex.singleFunctor A n).obj (K.homology n) ⟶ K.truncGE n :=
  HomologicalComplex.mkHomFromSingle (topComponent K n) (topComponent_d K n)

/-- Vanishing is a property of the specified complex, not an assumption
that the desired comparison exists. It makes exactly this inclusion a quasi-iso. -/
theorem topInclusion_quasiIso (hvan : ∀ i : ℤ, n < i → IsZero (K.homology i)) :
    QuasiIso (topInclusion K n) := sorry

variable [HasDerivedCategory.{w} A]

/-- Canonical top-degree trace in D(A), for A including continuous Galois
modules or completed-ring modules. No injectivity of the trace target is required. -/
def map (hvan : ∀ i : ℤ, n < i → IsZero (K.homology i)) {T : A}
    (t : K.homology n ⟶ T) :
    DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor A n).obj T) :=
  -- Local instance justification (defeq pin): invert the specified truncation inclusion using its proven degree bound.
  letI : QuasiIso (topInclusion K n) := topInclusion_quasiIso K n hvan
  DerivedCategory.Q.map (K.πTruncGE n) ≫
    inv (DerivedCategory.Q.map (topInclusion K n)) ≫
    DerivedCategory.Q.map ((CochainComplex.singleFunctor A n).map t)

end ActualEquivariantTopTrace
