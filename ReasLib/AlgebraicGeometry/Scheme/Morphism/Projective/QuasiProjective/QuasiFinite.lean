module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Normalization

/-!
# Quasi-projectivity of quasi-finite morphisms

This file records that a separated quasi-finite morphism of schemes is quasi-projective.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/-- A separated quasi-finite morphism of schemes is quasi-projective. -/
theorem QuasiFinite.quasiProjective
    {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : QuasiFinite f) (hsep : IsSeparated f) :
    QuasiProjective f := sorry

end Scheme.Hom

end AlgebraicGeometry
