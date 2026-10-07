module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Over an algebraically closed field `k`, a projective surface `X` admits a
closed subscheme with proper support and nonzero first cohomology of its
structure sheaf. -/
theorem exists_properClosedSubscheme_firstCohomology_structureSheaf_not_isZero
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Projective X.hom]
    (hXdim : topologicalKrullDim X.left = 2) :
    ∃ Z : X.left.IdealSheafData, Z.support ≠ ⊤ ∧
      ¬ IsZero (Scheme.Hom.cohomology (Z.subschemeι ≫ X.hom)
          (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules) 1) := sorry

/-- For every natural number `n`, a projective surface over an algebraically
closed field admits a proper closed subscheme whose structure-sheaf first
cohomology over the field has dimension greater than `n`. -/
theorem exists_properClosedSubscheme_firstCohomology_structureSheaf_finrank_gt
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Projective X.hom]
    (hXdim : topologicalKrullDim X.left = 2) (n : ℕ) :
    ∃ Z : X.left.IdealSheafData, Z.support ≠ ⊤ ∧
      n < Scheme.Hom.cohomologyFinrank (Z.subschemeι ≫ X.hom)
          (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules) 1 := sorry

/-- Over an algebraically closed field `k`, a projective surface `X` admits a
coherent `𝒪_X`-module `F` whose second cohomology is nonzero. -/
theorem exists_isCoherent_secondCohomology_not_isZero
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Projective X.hom]
    (hXdim : topologicalKrullDim X.left = 2) :
    ∃ (F : X.left.Modules) (_ : F.IsCoherent),
      ¬ IsZero (Scheme.Hom.cohomology X.hom F 2) := sorry

end AlgebraicGeometry.SchemeOverField
