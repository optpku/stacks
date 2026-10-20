module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface.Dimension
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearSubspace
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Lines on smooth projective hypersurfaces

Containment, Cartier divisors, associated sheaves, and self-intersection of lines
on smooth hypersurfaces in projective three-space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open AlgebraicGeometry.Scheme.Modules.Intersection
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Hypersurface

/-- Algebraic containment of a linear line in the hypersurface `V₊(F)`: the degree-`d` form lies
in the homogeneous ideal of the two linear forms. -/
def containsLine {k : Type u} [Field k] (F : MvPolynomial (Fin (3 + 1)) k)
    (ℓL : Fin 2 → MvPolynomial (Fin (3 + 1)) k) (hL : ∀ i, ℓL i ∈ grading k 3 1) : Prop :=
  F ∈ (lineIdeal ℓL hL).toIdeal

/-- Containment of the line in `V₊(F)` is equivalent to scheme-theoretic containment of the
corresponding closed immersions in `scheme k 3`. -/
theorem containsLine_iff {k : Type u} [Field k]
    (d : ℕ) (F : MvPolynomial (Fin (3 + 1)) k) (hF : F ∈ grading k 3 d)
    (ℓL : Fin 2 → MvPolynomial (Fin (3 + 1)) k) (hL : ∀ i, ℓL i ∈ grading k 3 1) :
    containsLine F ℓL hL ↔
      (closedImmersion 3 d F hF).ker ≤ (lineι ℓL hL).ker := sorry

/-- The inverse image of a linear line along the closed immersion of `V₊(F) ⊂ ℙ^3`, as an ideal
sheaf on the hypersurface. -/
def lineOnSurface {k : Type u} [Field k]
    (d : ℕ) (F : MvPolynomial (Fin (3 + 1)) k) (hF : F ∈ grading k 3 d)
    (ℓL : Fin 2 → MvPolynomial (Fin (3 + 1)) k) (hL : ∀ i, ℓL i ∈ grading k 3 1) :
    (scheme 3 d F hF).IdealSheafData :=
  (lineι ℓL hL).ker.comap (closedImmersion 3 d F hF)

/-- If the hypersurface contains the line, then `lineOnSurface` is isomorphic to the line,
compatibly with the closed immersions into `scheme k 3`. -/
theorem lineOnSurface_spec {k : Type u} [Field k]
    (d : ℕ) (F : MvPolynomial (Fin (3 + 1)) k) (hF : F ∈ grading k 3 d)
    (ℓL : Fin 2 → MvPolynomial (Fin (3 + 1)) k) (hL : ∀ i, ℓL i ∈ grading k 3 1)
    (hcontained : containsLine F ℓL hL) :
    ∃ e : (lineOnSurface d F hF ℓL hL).subscheme ≅ (lineι ℓL hL).ker.subscheme,
      e.hom ≫ (lineι ℓL hL).ker.subschemeι =
        (lineOnSurface d F hF ℓL hL).subschemeι ≫ closedImmersion 3 d F hF := sorry

/-- On a smooth hypersurface of positive degree, a linearly cut line contained in the
surface is an effective Cartier divisor. This excludes `F = 0`, which recovers `ℙ^3`
rather than a surface, on which a line has codimension two. The extra hypotheses are
explicit because they are not inferable from `lineOnSurface` alone. -/
theorem isEffectiveCartierDivisor_lineOnSurface {k : Type u} [Field k]
    (d : ℕ) (F : MvPolynomial (Fin (3 + 1)) k) (hF : F ∈ grading k 3 d)
    (hFne : F ≠ 0) (hd : 0 < d)
    (ℓL : Fin 2 → MvPolynomial (Fin (3 + 1)) k) (hL : ∀ i, ℓL i ∈ grading k 3 1)
    [Smooth (hom 3 d F hF)] (hLindep : LinearIndependent k ℓL)
    (hcontained : containsLine F ℓL hL) :
    IsEffectiveCartierDivisor (lineOnSurface d F hF ℓL hL).subschemeι := sorry

/-- The invertible sheaf associated to a linearly cut line contained in a smooth
positive-degree hypersurface. -/
def lineAssociatedSheaf {k : Type u} [Field k]
    (d : ℕ) (F : MvPolynomial (Fin (3 + 1)) k) (hF : F ∈ grading k 3 d)
    (hFne : F ≠ 0) (hd : 0 < d) [Smooth (hom 3 d F hF)]
    (ℓL : Fin 2 → MvPolynomial (Fin (3 + 1)) k)
    (hL : ∀ i, ℓL i ∈ grading k 3 1)
    (hLindep : LinearIndependent k ℓL)
    (hcontained : containsLine F ℓL hL) :
    (scheme 3 d F hF).Modules :=
  @associatedSheaf (scheme 3 d F hF) (lineOnSurface d F hF ℓL hL)
    (isEffectiveCartierDivisor_lineOnSurface d F hF hFne hd ℓL hL hLindep hcontained)

/-- The sheaf associated to a linearly cut line on a smooth positive-degree hypersurface
is invertible. -/
instance instInvertible_lineAssociatedSheaf {k : Type u} [Field k]
    (d : ℕ) (F : MvPolynomial (Fin (3 + 1)) k) (hF : F ∈ grading k 3 d)
    (hFne : F ≠ 0) (hd : 0 < d) [Smooth (hom 3 d F hF)]
    (ℓL : Fin 2 → MvPolynomial (Fin (3 + 1)) k)
    (hL : ∀ i, ℓL i ∈ grading k 3 1)
    (hLindep : LinearIndependent k ℓL)
    (hcontained : containsLine F ℓL hL) :
    Scheme.Modules.Invertible
      (lineAssociatedSheaf d F hF hFne hd ℓL hL hLindep hcontained) :=
  @Scheme.effectiveCartierDivisorAssociatedSheaf_isInvertible
    (scheme 3 d F hF) inferInstance (lineOnSurface d F hF ℓL hL).toSubobject
    (effectiveCartierIdealFact (lineOnSurface d F hF ℓL hL)
      (isEffectiveCartierDivisor_lineOnSurface d F hF hFne hd ℓL hL hLindep hcontained))

/-- Over an algebraically closed field `k`, if `S ⊂ ℙ^3_k` is a smooth
hypersurface of degree `d` containing a line `ℓ`, then the self-intersection of `ℓ` as a
divisor on `S` is `2 - d`. -/
theorem selfNumber_line_eq {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (F : MvPolynomial (Fin (3 + 1)) k) (hF : F ∈ grading k 3 d)
    (hFne : F ≠ 0) (hd : 0 < d) [Smooth (hom 3 d F hF)]
    (ℓL : Fin 2 → MvPolynomial (Fin (3 + 1)) k)
    (hL : ∀ i, ℓL i ∈ grading k 3 1)
    (hLindep : LinearIndependent k ℓL)
    (hcontained : containsLine F ℓL hL)
    [HasExt (Sheaf (Opens.grothendieckTopology
      (⊥ : (scheme 3 d F hF).IdealSheafData).subscheme.carrier) AddCommGrpCat.{u})] :
    selfNumber k (hom 3 d F hF) ⊥
      (hypersurface_topologicalKrullDim_eq_two d F hF hFne hd)
      (lineAssociatedSheaf d F hF hFne hd ℓL hL hLindep hcontained) =
      (2 : ℚ) - d := sorry

end AlgebraicGeometry.ProjectiveSpace.Hypersurface
