module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Module.Limit.FinitePresentation

/-!
# Finite-type ideal sheaves over inverse limits of schemes

Finite-type ideal-sheaf data descends along directed inverse limits of quasi-compact,
quasi-separated schemes with affine transition maps.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.Limit.FiniteType

/-- Finite-type ideal-sheaf data on a directed inverse limit of quasi-compact,
quasi-separated schemes with affine transition maps descends to some stage, and its comap is
the original ideal-sheaf data. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (𝓘 : c.pt.IdealSheafData) (h𝓘 : 𝓘.IsFiniteType) :
    ∃ (i : I) (𝓘i : (D.obj i).IdealSheafData),
      𝓘i.IsFiniteType ∧ 𝓘i.comap (c.π.app i) = 𝓘 := sorry

end AlgebraicGeometry.Scheme.IdealSheafData.Limit.FiniteType
