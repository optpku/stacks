module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Rees
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic

/-!
# Projectivity of blowups

Finite-type centers give projective blowup morphisms, and the degree-one twist of the canonical
Rees presentation is relatively ample.
-/

@[expose] public section

namespace AlgebraicGeometry.Blowup

universe u

noncomputable section

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- The structural morphism of a blowup along a finite-type quasi-coherent ideal sheaf is
projective. -/
theorem projective_of_isFiniteType (π : Blowup X I) [I.toModule.IsQuasicoherent]
    (hI : I.IsFiniteType) : Projective π.hom := sorry

/-- The degree-one twist in the canonical Rees presentation of a blowup along a finite-type
quasi-coherent ideal sheaf is relatively ample. -/
theorem twistOne_relativelyAmple_of_isFiniteType (π : Blowup X I)
    [I.toModule.IsQuasicoherent] (hI : I.IsFiniteType) :
    RelativelyAmple π.hom (π.reesPresentation.toRelativeProjPresentation.twist 1) := sorry

end

end AlgebraicGeometry.Blowup
