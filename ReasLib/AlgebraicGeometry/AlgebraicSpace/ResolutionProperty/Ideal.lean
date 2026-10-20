module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResolutionProperty.Descent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ResolutionProperty

/-!
# Resolution property via a pushforward ideal

For quasi-compact absolutely quasi-separated algebraic spaces with affine étale
descent data, the resolution property is equivalent to a finite locally free
epimorphic presentation of the associated pushforward ideal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ResolutionDescent

/-- A quasi-compact absolutely quasi-separated algebraic space has the resolution
property exactly when the pushforward of the descent ideal admits a finite locally
free epimorphic presentation. -/
@[stacks 0GV1]
theorem hasResolutionProperty_iff_epi_pushforward_ideal
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (sit : ResolutionDescent X) :
    SheafOfModules.HasResolutionProperty (structureSheaf X) ↔
      ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree)
        (q : E ⟶ (Modules.pushforward sit.π).obj sit.I.toModule),
        Epi q :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ResolutionDescent
