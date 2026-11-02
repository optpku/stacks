/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- A complex of modules over a Noetherian commutative ring is dualizing if its derived
extension along a faithfully flat map to another Noetherian ring is canonically
dualizing. -/
theorem of_faithfullyFlat
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
    (f : A →+* B) (hf : f.FaithfullyFlat)
    (CA : CanonicalClosedPresentation (A := A))
    (CB : CanonicalClosedPresentation (A := B))
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ((ModuleCat.derivedExtensionOfScalars f).obj K).IsCanonicalDualizingComplex CB) :
    K.IsCanonicalDualizingComplex CA := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
