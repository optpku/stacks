module

public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- An equivalence between the categories of quasi-coherent modules on quasi-compact,
quasi-separated schemes is naturally isomorphic to pullback along a scheme isomorphism
followed by tensoring with an invertible module on the target scheme. -/
theorem equivalence_pullback_tensor_invertible
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) [F.IsEquivalence] :
    ∃ (f : Y ≅ X) (L : Scheme.QCoh Y),
      Scheme.Modules.Invertible L.obj ∧
        Nonempty (F ≅ Scheme.QCoh.pullback f.hom ⋙ Scheme.QCoh.tensorRight L) := sorry

end AlgebraicGeometry.Scheme.QCoh
