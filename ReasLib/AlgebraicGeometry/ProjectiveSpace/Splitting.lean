module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Splitting
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.LinearForm
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- A finite locally free module on the projective plane is split if and only if any
integer twist of it is split. -/
theorem isSplit_twist_iff {k : Type u} [Field k]
    (E : (scheme k 2).Modules) [E.IsFiniteLocallyFree] (n : ℤ) :
    IsSplit E ↔ IsSplit (twist k 2 E n) := sorry

/-- Every integer twist of a split finite locally free module on the projective plane has
zero first cohomology. -/
theorem cohomology_one_isZero_of_isSplit {k : Type u} [Field k]
    (E : (scheme k 2).Modules) [E.IsFiniteLocallyFree] [IsSplit E] (n : ℤ) :
    IsZero (Scheme.Hom.cohomology (toSpec k 2) (twist k 2 E n) 1) := sorry

/-- The cokernel of a morphism defined by three homogeneous linear forms on the projective
plane, not all zero, is finite locally free if and only if the forms are linearly independent. -/
theorem cokernel_isFiniteLocallyFree_iff {k : Type u} [Field k]
    (L : Fin (2 + 1) → MvPolynomial (Fin (2 + 1)) k)
    (hL : ∀ i, L i ∈ grading k 2 1) (h_ne : ∃ i, L i ≠ 0) :
    (cokernel (linearFormHom L hL)).IsFiniteLocallyFree ↔ LinearIndependent k L := sorry

/-- The cokernel of the morphism defined by the three homogeneous coordinates on the
projective plane is finite locally free. -/
instance coordinateLinearFormHom_cokernel_isFiniteLocallyFree (k : Type u) [Field k] :
    (cokernel (coordinateLinearFormHom k)).IsFiniteLocallyFree := sorry

/-- A finite locally free cokernel of a morphism defined by three homogeneous linear forms
on the projective plane, not all zero, is not split. -/
theorem cokernel_not_isSplit {k : Type u} [Field k]
    (L : Fin (2 + 1) → MvPolynomial (Fin (2 + 1)) k)
    (hL : ∀ i, L i ∈ grading k 2 1) (h_ne : ∃ i, L i ≠ 0)
    [(cokernel (linearFormHom L hL)).IsFiniteLocallyFree] :
    ¬ IsSplit (cokernel (linearFormHom L hL)) := sorry

end AlgebraicGeometry.ProjectiveSpace
