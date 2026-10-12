/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.AssociatedPoints.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay

@[expose] public section

open AlgebraicGeometry CategoryTheory SheafOfModules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace RelativeDualizingSheaf

/-- Generic-point étaleness for a quasi-finite Gorenstein morphism with a Cohen–Macaulay
source yields a unique comparison from the different's associated sheaf to the relative
dualizing sheaf that preserves the distinguished sections. -/
theorem existsUnique_differentAssociatedSheafIso_of_genericEtale
    {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
    [Scheme.Hom.QuasiFinite f] [AlgebraicGeometry.Gorenstein f]
    [Scheme.CohenMacaulay Y]
    (W : f.RelativeDualizingSheaf) (τ : sections W.module.obj)
    (hτ : W.IsTraceSection τ)
    (h_generic : ∀ y : Y, y ∈ genericPoints Y → f.EtaleAt y) :
    ∃ hR : IsEffectiveCartierDivisor (W.different τ).subschemeι,
      ∃! e : @IdealSheafData.associatedSheaf Y (W.different τ) hR ≅ W.module.obj,
        SheafOfModules.sectionsMap e.hom
          (@IdealSheafData.canonicalSection Y (W.different τ) hR) = τ := sorry

end RelativeDualizingSheaf
end Hom
end Scheme
end AlgebraicGeometry
