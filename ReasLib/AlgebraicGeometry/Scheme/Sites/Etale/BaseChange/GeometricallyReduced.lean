module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.GeometricallyConnectedFiber.EtaleCover

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- A flat locally finitely presented morphism with geometrically reduced fibres
admits étale-local factorizations through small étale objects of the base by
quasi-compact morphisms with geometrically connected fibres. -/
theorem hasConnectedFactorizationCover_of_geometricallyReduced {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    HasConnectedFactorizationCover f := sorry

namespace BaseChange

variable {X Y S T : Scheme.{u}}

/-- For a cartesian square, flatness, local finite presentation, and geometrically
reduced fibres make the canonical set-valued étale base-change comparison
invertible for every sheaf on the changed base. -/
theorem setMap_isIso_of_geometricallyReduced
    (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f]
    (cart : IsPullback h e f g) (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    IsIso (setMap f h e g cart F) := sorry

/-- Every component of the canonical set-valued étale base-change comparison is
invertible in a cartesian square whose original morphism is flat, locally finitely
presented, and has geometrically reduced fibres. -/
theorem setMap_isIso_of_geometricallyReduced_app
    (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f]
    (cart : IsPullback h e f g) (F : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : X.Etaleᵒᵖ) :
    IsIso ((setMap f h e g cart F).hom.app U) := sorry

end BaseChange

end AlgebraicGeometry.Scheme.Etale
