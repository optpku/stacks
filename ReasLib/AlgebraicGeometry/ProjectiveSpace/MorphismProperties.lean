module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

namespace AlgebraicGeometry.ProjectiveSpace

universe u

/-- The canonical projection from projective `n`-space over a scheme is of finite type. -/
instance toBase_finiteType (n : ℕ) (S : Scheme.{u}) :
    Scheme.Hom.FiniteType (toBase n S) := sorry

/-- The canonical projection from projective `n`-space over a scheme is smooth. -/
instance toBase_smooth (n : ℕ) (S : Scheme.{u}) : Smooth (toBase n S) := sorry

/-- The canonical projection from projective `n`-space over a scheme is separated. -/
instance toBase_isSeparated (n : ℕ) (S : Scheme.{u}) : IsSeparated (toBase n S) := sorry

/-- The canonical projection from projective `n`-space over a scheme is universally closed. -/
instance toBase_universallyClosed (n : ℕ) (S : Scheme.{u}) :
    UniversallyClosed (toBase n S) := sorry

end AlgebraicGeometry.ProjectiveSpace
