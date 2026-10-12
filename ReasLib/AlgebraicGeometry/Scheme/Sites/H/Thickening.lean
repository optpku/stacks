/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenCovering
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenPresentation.Affine
public import ReasLib.CategoryTheory.Sites.Singleton

/-!
# Invariance of h sheaves under thickenings

Sheaves of types for chosen big h-site slices and their affine subsites send
finite-presentation thickenings to bijections on sections.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.ChosenBigHSite.Sheaf

/-- A sheaf of types on a chosen big h-site slice sends a finite-presentation
thickening contravariantly to a bijection on sections. -/
theorem map_bijective_of_isThickening
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : Sheaf (bigTopology Schh S) (Type w)) {X X' : Over S}
    (f : X ⟶ X')
    [IsThickening ((ChosenBigSite.sliceToScheme Schh S).map f)]
    [Scheme.Hom.FinitePresentation ((ChosenBigSite.sliceToScheme Schh S).map f)] :
    Function.Bijective (F.obj.map f.op) := sorry

/-- A sheaf of types on the affine subsite of a chosen big h-site slice sends
a finite-presentation thickening contravariantly to a bijection on sections. -/
theorem affineMap_bijective_of_isThickening
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : Sheaf (bigAffineTopology Schh S) (Type w))
    {X X' : ChosenBigSite.affineSite Schh S} (f : X ⟶ X')
    [IsThickening ((ChosenBigSite.affineToScheme Schh S).map f)]
    [Scheme.Hom.FinitePresentation ((ChosenBigSite.affineToScheme Schh S).map f)] :
    Function.Bijective (F.obj.map f.op) := sorry

end AlgebraicGeometry.ChosenBigHSite.Sheaf
