/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Intersection

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.SpecialFiber

/-- The residue-field degree of the global-sections algebra of a special-fibre component. -/
noncomputable def componentWeight
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (i : irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) : ℕ :=
  @Module.finrank
    ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
    (Scheme.Hom.globalSectionsAlg (componentToResidueField f i))
    inferInstance inferInstance
    (@Algebra.toModule
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
      (Scheme.Hom.globalSectionsAlg (componentToResidueField f i))
      inferInstance inferInstance
      (Scheme.Hom.globalSectionsAlgebra (componentToResidueField f i)))

end AlgebraicGeometry.Scheme.Hom.SpecialFiber
