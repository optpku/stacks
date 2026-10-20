module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Separated finite-presentation factorizations

This module records closed-immersion factorizations of finite-type separated morphisms through
separated morphisms of finite presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.FinitePresentation

/-- A finite-type separated morphism over a quasi-compact and quasi-separated base factors as a
closed immersion followed by a separated morphism of finite presentation. -/
theorem exists_separated_closedImmersion_factorization_of_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f] [IsSeparated f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    (MorphismProperty.comp @IsClosedImmersion
      ((@Scheme.Hom.FinitePresentation : MorphismProperty Scheme) ⊓ @IsSeparated)) f := sorry

end AlgebraicGeometry.Scheme.Hom.FinitePresentation
