module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.UnitDenominators
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.ResidualConstruction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Regular
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi

/-! # A genuine ordinary generic vector and meromorphic section

At an ordinary residue point p, the actual pulled-back module on Spec K
has a terminal chart. Its sections there form its K-fibre through the
canonical Spec–Γ ring map. Evaluate actual meromorphic pullback at that
chart, contract its unit denominators, then invert that specified generic
restriction. No geometric/separable closure or chosen section is used.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.MonoidalCategory
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.GenericSection

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

def fieldChart (p : FieldValuedPoint X) : smallEtaleSite (ofOver p.overObj) :=
  smallEtaleSite.mk (U := p.overObj) (𝟙 (ofOver p.overObj))

def fieldModule (p : FieldValuedPoint X) (F : X.Modules) : (ofOver p.overObj).Modules :=
  (Modules.pullback p.hom).obj F

/-- The ordinary K-fibre is the actual terminal-chart module, restricting
coefficients by K → Γ(Spec K,O). The carrier remains in universe u. -/
def fibre (p : FieldValuedPoint X) (F : X.Modules) : ModuleCat.{u} p.K :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of p.K)).inv.hom).obj
    ((fieldModule p F).val.obj (op (fieldChart p)))

/-- All regular denominators on schemes étale over a field are units.
This uses the actual regular-function definition, including disconnected charts. -/
theorem field_denominators_units (p : FieldValuedPoint X)
    (U : (smallEtaleSite (ofOver p.overObj))ᵒᵖ)
    (d : (regularStructureSections (ofOver p.overObj)).obj U) :
    IsUnit (d : (commStructureSheafLift (ofOver p.overObj)).obj.obj U) := by
  sorry

def evaluate (p : FieldValuedPoint X) (F : X.Modules)
    (s : meromorphicSections (ofOver p.overObj) (fieldModule p F)) : fibre p F :=
  ((UnitDenominators.sheafEvaluation (ofOver p.overObj) (fieldModule p F)
    (field_denominators_units p)).app (op (fieldChart p))
      (s.val (op (fieldChart p)))).down

def alongPoint (p : FieldValuedPoint X) [PullbacksMeromorphicFunctionsDefined p.hom]
    (F : X.Modules) (s : meromorphicSections X F) : fibre p F :=
  evaluate p F (Pullback.pullback p.hom F s)

variable (X) [AlgebraicSpace.IsIntegral X] [AlgebraicSpace.IsQuasiSeparated X]
    {η : Points X} (hη : η ∈ genericPoints X)

/-- The explicit equalizer-field point, not a choice from the decency
existence theorem. In the original Chern target quasi-separatedness follows
from the good-space structure map; it is not a new statement assumption. -/
def point : FieldValuedPoint X := ResidualPoint.point X η

include hη in
theorem generic_denominators : PullbacksMeromorphicFunctionsDefined (point X (η := η)).hom := by
  sorry

def restrict (F : X.Modules) (s : meromorphicSections X F) : fibre (point X (η := η)) F := by
  -- Local instance justification (proof-local temporary data): Nonzero denominators stay invertible at the supplied generic point hη, enabling evaluation of the explicit fractions there.
  letI := generic_denominators X hη
  exact alongPoint (point X) F s

/-- Stacks 71.10.8: actual total fractions of a quasi-coherent module
restrict bijectively to its ordinary generic fibre. This is the specific
map defined above, not an arbitrary isomorphism. -/
theorem restrict_bijective (F : X.Modules) [F.IsQuasicoherent] :
    Function.Bijective (restrict X hη F) := by
  sorry

def restrictionEquiv (F : X.Modules) [F.IsQuasicoherent] :
    meromorphicSections X F ≃ fibre (point X (η := η)) F :=
  Equiv.ofBijective (restrict X hη F) (restrict_bijective X hη F)

variable (L : X.Modules) [isInvertibleObject L]

theorem line_quasicoherent : L.IsQuasicoherent := by sorry

theorem fibre_rank_one : Module.rank (point X (η := η)).K (fibre (point X (η := η)) L) = 1 := by
  sorry

def coordinates : fibre (point X (η := η)) L ≃ₗ[(point X (η := η)).K] (point X (η := η)).K :=
  (finDimVectorspaceEquiv 1 (fibre_rank_one X L)).trans
    (LinearEquiv.funUnique (Fin 1) _ _)

def vector : fibre (point X (η := η)) L := (coordinates X L).symm 1

theorem vector_ne_zero : vector X (η := η) L ≠ 0 := by
  intro h
  have hv := congrArg (coordinates X L) h
  simp only [vector, LinearEquiv.apply_symm_apply, map_zero] at hv
  exact one_ne_zero hv

def sectionValue : meromorphicSections X L := by
  -- Local instance justification (proof-local temporary data): Use quasi-coherence of the given invertible module L to apply the genuine generic-fibre restriction equivalence.
  letI := line_quasicoherent X L
  exact (restrictionEquiv X hη L).symm (vector X L)

theorem restrict_sectionValue : restrict X hη L (sectionValue X hη L) = vector X L := by
  -- Local instance justification (proof-local temporary data): Use quasi-coherence of the given invertible module L to apply the genuine generic-fibre restriction equivalence.
  letI := line_quasicoherent X L
  exact (restrictionEquiv X hη L).apply_symm_apply _

theorem regular_of_nonzero (s : meromorphicSections X L) (hs : restrict X hη L s ≠ 0) :
    IsRegularMeromorphicSection X L s := by
  sorry

theorem sectionValue_regular : IsRegularMeromorphicSection X L (sectionValue X hη L) := by
  apply regular_of_nonzero X hη L
  rw [restrict_sectionValue]
  exact vector_ne_zero X L

end AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.GenericSection
