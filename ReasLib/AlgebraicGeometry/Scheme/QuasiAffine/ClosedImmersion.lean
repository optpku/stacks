module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A homeomorphic closed immersion of schemes preserves and reflects quasi-affineness. -/
theorem isQuasiAffine_iff_of_isClosedImmersion_isHomeomorph
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (hi : IsHomeomorph i) :
    X.IsQuasiAffine ↔ Z.IsQuasiAffine := sorry

/-- A homeomorphic closed immersion between Noetherian schemes preserves quasi-affineness. -/
theorem isQuasiAffine_iff_of_isClosedImmersion_isHomeomorph_of_isNoetherian
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsNoetherian X] [IsNoetherian Z]
    [IsClosedImmersion i] (hi : IsHomeomorph i) :
    X.IsQuasiAffine ↔ Z.IsQuasiAffine := sorry

end AlgebraicGeometry.Scheme
