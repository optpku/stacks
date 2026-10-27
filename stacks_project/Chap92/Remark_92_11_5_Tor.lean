/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Cotangent.PolynomialSiteTor
import StacksCheckRecall

/-!
# Tor sheaves of the kernel ideal on the polynomial site

The objectwise derived extension of scalars of the kernel ideal gives the Tor sheaves
on the polynomial site and their degree-zero conormal comparison.
-/

@[expose] public section

open CategoryTheory
open CommAlgCat.Over.Polynomial.Site

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/- Remark 92.11.5. The objectwise Tor functor of the kernel ideal. -/
#check (CommAlgCat.Over.Polynomial.Site.kernelTorCov A B :
    ℕ → Algebra.PolynomialOver A B ⥤ ModuleCat.{u} B)

/- Remark 92.11.5. The sheaf of Tor modules of the kernel ideal. -/
#check (CommAlgCat.Over.Polynomial.Site.kernelTorSheaf A B :
    ℕ → (Algebra.PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)

/- Remark 92.11.5. Degree-zero Tor is the conormal sheaf. -/
#check (CommAlgCat.Over.Polynomial.Site.kernelTorZeroIso A B :
    kernelTorSheaf A B 0 ≅ conormalSheaf A B)
