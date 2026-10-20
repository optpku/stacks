/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealComplement.Cech
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open LocalizedModule.Away.Cech

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace IdealComplement

/- Exercise 111.43.2: for a ring `A`, a finite family `f : Fin t → A` generating an
ideal `I`, and an `A`-module `M`, the cohomology of the ordered Čech complex of
localizations of `M` away from products of the entries of `f` computes
`H^n(U, tilde M)`, where `U` is the complement of `V(I)` in `Spec A`. -/
@[stacks 0DAK] #check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.orderedCechHomology_iso :
    ∀ {A : Type u} [CommRing A] {t : ℕ}
      (f : Fin t → A) (M : ModuleCat A) (n : ℕ),
      IsIsomorphic ((Ordered.complex f M).homology n)
        (cohomology (Ideal.span (Set.range f))
          ((tilde M).restrict (idealComplementOpens (Ideal.span (Set.range f))).ι) n))

end IdealComplement

end AlgebraicGeometry.Scheme.Modules
