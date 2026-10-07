module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.QuasiFinite

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsPureAlong

/-- At a Noetherian target stalk, purity along a fibre is equivalent to universal purity
along that fibre. -/
theorem iff_universally_of_noetherian_stalk {X S : Scheme.{u}} (F : X.Modules)
    (f : X ⟶ S) [f.FiniteType] [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    [IsNoetherianRing (S.presheaf.stalk s)] :
    F.IsPureAlong f s ↔ F.IsUniversallyPureAlong f s := sorry

end AlgebraicGeometry.Scheme.Modules.IsPureAlong
