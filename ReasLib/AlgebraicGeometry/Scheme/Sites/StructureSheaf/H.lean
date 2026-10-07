module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Proper
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.RelativeRepresentability
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.CategoryTheory.Sites.Singleton

/-!
# Failure of h-descent for the structure presheaf

This module records a singleton h-cover on which the global-sections structure presheaf does
not satisfy descent.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Site

/-- The global-sections structure presheaf fails descent along a nonisomorphic surjective
closed immersion of finite presentation between affine schemes. -/
theorem structurePresheaf_not_isSheafFor_hCover {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y] [Surjective f] [IsClosedImmersion f]
    [Hom.FinitePresentation f] (h_not_iso : ¬ IsIso f) :
    ¬ Presieve.IsSheafFor
      (structurePresheaf (Functor.id Scheme.{u}) ⋙ CategoryTheory.forget RingCat.{u})
      (Presieve.singleton f) := sorry

/-- The underlying structure presheaf on schemes over a nonempty base is not an h-sheaf. -/
theorem structurePresheaf_not_isSheaf_hTopology (S : Scheme.{u}) [Nonempty S] :
    ¬ Presieve.IsSheaf ((Scheme.hPrecoverage.toGrothendieck).over S)
      (Scheme.Over.GlobalSections.functor S) := sorry

end AlgebraicGeometry.Scheme.Site

namespace AlgebraicGeometry.Scheme

/-- On schemes over a nonempty base, the h topology is not subcanonical. -/
theorem hTopology_not_subcanonical (S : Scheme.{u}) [Nonempty S] :
    ¬ ((hPrecoverage.toGrothendieck).over S).Subcanonical := sorry

end AlgebraicGeometry.Scheme
