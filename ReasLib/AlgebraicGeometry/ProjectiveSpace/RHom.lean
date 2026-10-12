/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Derived.Over
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Linear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

/-!
# Derived Hom on projective space

This file specializes enriched derived Hom to modules on standard projective space over its
base ring.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The canonical derived Hom over the base ring between two derived module sheaves on standard
projective space. -/
noncomputable abbrev rHom
    (A : Type u) [CommRing A] (n : ℕ)
    (E K : RingedSpace.ModuleDerived (scheme A n).toRingedSpace) :=
  (@CategoryTheory.CochainComplex.Enriched.Over.RHom.functor
      A inferInstance (scheme A n).Modules inferInstance inferInstance inferInstance inferInstance
      (@CategoryTheory.CochainComplex.Enriched.Over.RHom.hasRightDerivedFunctor
        A inferInstance (scheme A n).Modules inferInstance inferInstance inferInstance
        (SheafOfModules.isGrothendieckAbelian (scheme A n).ringCatSheaf))).obj (Opposite.op E, K)

end AlgebraicGeometry.ProjectiveSpace

end
