module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.CoordinateIdeal
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.JacobsonSpace

/-!
# Smooth closed points on plane curves

An infinite-field plane curve with a smooth point has a smooth closed point with
controlled separable residue-field degree.
-/

@[expose] public section

open CategoryTheory Set TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme

/-- An equidimensional plane curve without embedded points over an infinite field, defined
by `F` and smooth at some point, has a smooth closed point whose residue field is finite
separable of degree at most `F.totalDegree`. -/
theorem exists_smooth_closedPoint_finrank_le_totalDegree
    (k : Type u) [Field k] [Infinite k]
    (Z : (ProjectiveSpace.scheme k 2).IdealSheafData)
    (h_componentDim : ∀ C : irreducibleComponents Z.subscheme,
      topologicalKrullDim (C : Set Z.subscheme) = 1)
    (h_noEmbeddedPoints : Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme))
    (F : MvPolynomial (Fin 3) k)
    (h_generator : coordinateIdeal 2 Z = Ideal.span {F})
    (h_smooth : ∃ z' : Z.subscheme,
      (Z.subschemeι ≫ ProjectiveSpace.toSpec k 2).SmoothAt z') :
    let X : SchemeOverField k :=
      Over.mk (Z.subschemeι ≫ ProjectiveSpace.toSpec k 2)
    ∃ z : X.left, z ∈ closedPoints X.left ∧ X.hom.SmoothAt z ∧
      FiniteDimensional k (X.left.residueField z) ∧
      Algebra.IsSeparable k (X.left.residueField z) ∧
      Module.finrank k (X.left.residueField z) ≤ F.totalDegree := sorry

end AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
