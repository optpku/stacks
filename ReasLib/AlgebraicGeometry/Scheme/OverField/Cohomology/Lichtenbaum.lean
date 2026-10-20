module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Cohomology.Dimension

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- For a nonempty separated algebraic scheme over a field, vanishing of top-degree cohomology
for every coherent module, vanishing for every quasicoherent module, and nonproperness of every
top-dimensional irreducible component are equivalent. -/
theorem topCohomology_isZero_tfae {k : Type u} [Field k]
    (X : SchemeOverField k) [Algebraic X] [IsSeparated X.hom] [Nonempty X.left]
    (d : ℕ) (h_dimension : topologicalKrullDim X.left = d) :
    List.TFAE [
      ∀ F : X.left.Modules,
        F.IsCoherent → IsZero (Scheme.Modules.cohomology F d),
      ∀ F : X.left.Modules,
        F.IsQuasicoherent → IsZero (Scheme.Modules.cohomology F d),
      ∀ Z : irreducibleComponents X.left,
        topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = d →
          ¬ IsProper (X.left.irreducibleComponentSubschemeι Z ≫ X.hom)] := sorry

end AlgebraicGeometry.SchemeOverField

end
