/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FlatExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 47.22.2: a flat map of Noetherian commutative rings that is an isomorphism
modulo an ideal whose extension lies in the target Jacobson radical carries dualizing
complexes to dualizing complexes by derived extension of scalars. -/
@[stacks 0DWC]
#check (CategoryTheory.DerivedCategory.IsDualizingComplex.flatExtension :
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
    (f : A →+* B) (hflat : f.Flat)
    (I : Ideal A) (hquot : Function.Bijective (f.quotientByIdeal I))
    (hIB : I.map f ≤ Ring.jacobson B)
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA),
    ((ModuleCat.derivedExtensionOfScalars f).obj ω).IsDualizingComplex HB)
