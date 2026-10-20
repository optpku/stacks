module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallToBig.Derived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion

/-!
# Proper small-to-big étale direct-image comparisons

Proper direct image commutes with small-to-big inverse image on sheaves of sets
and on bounded-below complexes with torsion cohomology. For finite morphisms
the derived comparison is invertible on every unbounded complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Adjunction
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory.Sheaf
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Functor (associator isoWhiskerLeft isoWhiskerRight leftUnitor rightUnitor)
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

variable (f : Y ⟶ X)

/-- For a proper morphism of algebraic spaces, the canonical small-to-big
étale direct-image comparison on sheaves of sets is an isomorphism. -/
instance proper_smallBigPushforward_isIso [Proper f] :
    IsIso (smallBigPushforwardHom f) := sorry

/-- For a proper morphism, the canonical small-to-big étale derived direct-image
comparison is an isomorphism on bounded-below complexes with locally torsion cohomology. -/
theorem proper_smallBigDerivedPushforward_plus_isIso [Proper f]
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})) K) :
    IsIso ((plusSmallBigPushforwardHom f).app K) := sorry

variable [IsGrothendieckAbelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [IsGrothendieckAbelian (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})]

/-- For a finite morphism, the canonical small-to-big étale derived direct-image
comparison is an isomorphism on every unbounded complex. -/
instance finite_smallBigDerivedPushforward_isIso [IsFinite f]
    (K : DerivedCategory (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})) :
    IsIso ((unboundedSmallBigPushforwardHom f).app K) := sorry


end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

end

end
