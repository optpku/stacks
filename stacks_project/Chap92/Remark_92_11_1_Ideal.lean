/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Cotangent.PolynomialSiteVanishing
import StacksCheckRecall

/-!
# Kernel and conormal presheaves on the polynomial site

The reusable kernel, conormal, and differential-map API is provided by the
shared polynomial-site cotangent owner.
-/

@[expose] public section

open CategoryTheory
open CommAlgCat.Over.Polynomial.Site

universe u

namespace CommAlgCat.Over.Polynomial.Site

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/- Remark 92.11.1 support API: the kernel presheaf is the shared construction. -/
@[stacks 08R7] #check (CommAlgCat.Over.Polynomial.Site.kernelPresheaf A B :
  (Algebra.PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})

end CommAlgCat.Over.Polynomial.Site
