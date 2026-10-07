module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- An open subscheme of a quasi-separated scheme is quasi-separated. -/
theorem openQuasiSeparatedSpace
    {Y : Scheme.{u}} [QuasiSeparatedSpace Y] (V : Y.Opens) :
    QuasiSeparatedSpace V := sorry

namespace Hom

/-- A quasi-compact morphism has compact inverse image of a compact open subscheme. -/
theorem inverseImageOpenCompactSpace
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (V : Y.Opens) [CompactSpace V] : CompactSpace (f ⁻¹ᵁ V) := sorry

/-- The inverse image of an open in a quasi-separated scheme along a quasi-separated morphism
is quasi-separated. -/
theorem inverseImageOpenQuasiSeparatedSpace
    {X Y : Scheme.{u}} [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [QuasiSeparated f] (V : Y.Opens) :
    QuasiSeparatedSpace (f ⁻¹ᵁ V) := sorry

/-- The inclusion of the inverse image of a compact open under a quasi-compact,
quasi-separated morphism is quasi-compact. -/
theorem inverseImageOpenιQuasiCompact
    {X Y : Scheme.{u}} [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (V : Y.Opens) [CompactSpace V] : QuasiCompact (f ⁻¹ᵁ V).ι := sorry

end Hom

end AlgebraicGeometry.Scheme
