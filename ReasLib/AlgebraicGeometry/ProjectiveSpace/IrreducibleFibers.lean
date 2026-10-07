module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Composition

/-!
# Projective schemes with irreducible fibres over the projective line

Constant-dimensional irreducible fibres determine the dimension of a reduced projective
scheme and force each maximal-dimensional component to fill every fibre.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsReduced X]
  {f : X ⟶ ProjectiveSpace.scheme k 1}
  (h_projective : ∃ (n : ℕ) (embedding : X ⟶ ProjectiveSpace.scheme k n),
    IsClosedImmersion embedding ∧
      embedding ≫ ProjectiveSpace.toSpec k n = X ↘ Spec (CommRingCat.of k))
  (hf : f ≫ ProjectiveSpace.toSpec k 1 = X ↘ Spec (CommRingCat.of k))
  {d : ℕ} (h_irr : ∀ t, IrreducibleSpace (f.fiber t))
  (h_dim : ∀ t, topologicalKrullDim (f.fiber t) = (d : WithBot ℕ∞))

include h_projective hf h_irr h_dim

/-- A reduced projective scheme over a field mapping to the projective line with
nonempty irreducible fibres of constant dimension `d` has dimension `d + 1`. -/
theorem topologicalKrullDim_eq_succ_of_irreducibleFibers :
    topologicalKrullDim X = (d + 1 : WithBot ℕ∞) := sorry

section

variable (X0 : irreducibleComponents X)
  (hX0 : topologicalKrullDim (X.irreducibleComponentSubscheme X0) =
    (d + 1 : WithBot ℕ∞))
  (t : ProjectiveSpace.scheme k 1)

include hX0

/-- Every fibre of the restriction to an irreducible component of dimension `d + 1`
has dimension `d` when a reduced projective scheme over a field maps to the projective
line with nonempty irreducible fibres of constant dimension `d`. -/
theorem fiber_topologicalKrullDim_irreducibleComponent :
    topologicalKrullDim ((X.irreducibleComponentSubschemeι X0 ≫ f).fiber t) =
      (d : WithBot ℕ∞) := sorry

/-- For a reduced projective scheme over a field mapping to the projective line with
nonempty irreducible fibres of constant dimension `d`, the fibre comparison from an
irreducible component of dimension `d + 1` is surjective. -/
theorem surjective_compFiberToBaseFiber_irreducibleComponent :
    Surjective (compFiberToBaseFiber (X.irreducibleComponentSubschemeι X0) f t) := sorry

/-- For a reduced projective scheme over a field mapping to the projective line with
nonempty irreducible fibres of constant dimension `d`, the fibres of its restriction
to an irreducible component of dimension `d + 1` have the same underlying subsets
of the scheme as the original fibres. -/
theorem range_fiberι_irreducibleComponent_eq :
    Set.range ((X.irreducibleComponentSubschemeι X0 ≫ f).fiberι t ≫
      X.irreducibleComponentSubschemeι X0) =
      Set.range (f.fiberι t) := sorry

end

/-- A reduced projective scheme over a field mapping to the projective line with
nonempty irreducible fibres of constant finite dimension is irreducible. -/
theorem irreducibleSpace_of_irreducibleFibers : IrreducibleSpace X := sorry

end AlgebraicGeometry.Scheme.Hom
