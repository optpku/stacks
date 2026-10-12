/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition
public import ReasLib.CategoryTheory.Adjunction.RightIso

@[expose] public section

/-!
# Composition of derived coextension of scalars

Iterating derived coextension along two composable ring homomorphisms is canonically
isomorphic to derived coextension along their composite.
-/

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedCoextension

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- Iterated derived coextension along composable ring homomorphisms is canonically isomorphic
to derived coextension along their composite. -/
noncomputable def compIso (f : A →+* B) (g : B →+* C) :
    derivedCoextensionOfScalars f ⋙ derivedCoextensionOfScalars g ≅
      derivedCoextensionOfScalars (g.comp f) :=
  Adjunction.rightAdjointIsoOfLeftIso
    (DerivedRestriction.compIso f g).symm
    ((derivedRestrictionCoextensionAdjunction g).comp
      (derivedRestrictionCoextensionAdjunction f))
    (derivedRestrictionCoextensionAdjunction (g.comp f))

/-- The objectwise comparison between iterated and direct derived coextension of scalars. -/
noncomputable abbrev compObjIso (f : A →+* B) (g : B →+* C)
    (K : DerivedCategory (ModuleCat.{u, u} A)) :
    (derivedCoextensionOfScalars g).obj
        ((derivedCoextensionOfScalars f).obj K) ≅
      (derivedCoextensionOfScalars (g.comp f)).obj K :=
  (compIso f g).app K

end CategoryTheory.ModuleCat.DerivedCoextension
