/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Torsion
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.IdealPower.DerivedBaseChange

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Derived extension of scalars along `f` carries complexes with `I`-power-torsion
cohomology to complexes with `(I.map f)`-power-torsion cohomology when `I` is finitely
generated. -/
theorem mapsExtensionOfFG (f : A →+* B) (I : Ideal A) (hI : I.FG) :
    DerivedCategory.cohomologyIn
        (fun M : ModuleCat A ↦ Module.IsIdealPowerTorsion I M) ≤
      (DerivedCategory.cohomologyIn
          (fun M : ModuleCat B ↦ Module.IsIdealPowerTorsion (I.map f) M)).inverseImage
        (ModuleCat.derivedExtensionOfScalars f) := sorry

/-- Derived extension of scalars restricted to derived objects with ideal-power-torsion
cohomology, for a finitely generated ideal. -/
noncomputable def extensionOfFG (f : A →+* B) (I : Ideal A) (hI : I.FG) :
    DerivedCategory.IdealPowerTorsion I ⥤
      DerivedCategory.IdealPowerTorsion (I.map f) :=
  ObjectProperty.FullSubcategory.restrict
    (ModuleCat.derivedExtensionOfScalars f) (mapsExtensionOfFG f I hI)

/-- Forgetting the torsion condition identifies `extensionOfFG` on objects with ambient
derived extension of scalars. -/
theorem extensionOfFG_obj (f : A →+* B) (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory.IdealPowerTorsion I) :
    ((extensionOfFG f I hI).obj K).obj =
      (ModuleCat.derivedExtensionOfScalars f).obj K.obj := sorry

/-- The canonical inclusion comparison for derived extension restricted to
ideal-power-torsion objects. -/
noncomputable def extensionOfFGCompιIso (f : A →+* B) (I : Ideal A) (hI : I.FG) :
    extensionOfFG f I hI ⋙ DerivedCategory.IdealPowerTorsion.inclusion (I.map f) ≅
      DerivedCategory.IdealPowerTorsion.inclusion I ⋙
        ModuleCat.derivedExtensionOfScalars f :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (ModuleCat.derivedExtensionOfScalars f) (mapsExtensionOfFG f I hI)

/-- The forward component of `extensionOfFGCompιIso` is the identity of the underlying
derived-extension object. -/
theorem extensionOfFGCompιIso_hom_app (f : A →+* B) (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory.IdealPowerTorsion I) :
    (extensionOfFGCompιIso f I hI).hom.app K =
      𝟙 ((ModuleCat.derivedExtensionOfScalars f).obj K.obj) := sorry

end CategoryTheory.ModuleCat.IdealPower.DerivedBaseChange
