/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.Cech.Nerve.Coskeletal
import StacksCheckRecall

/-!
@stack 018I

# Lemma 14.20.3 compatibility facade

The reusable owner is split into the degree-zero classification of maps into a Cech nerve and the
equivalent categorical assertion that a Cech nerve is `1`-coskeletal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject
open scoped Simplicial

universe u v

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C]
variable (f : Arrow C) (V : SimplicialObject C)
variable [HasPullbacks C]

/- Lemma 14.20.3 (1): maps into the Cech nerve are exactly maps between the corresponding
`1`-truncations. -/
@[stacks 018I "Lemma 14.20.3 (1)"]
#check (cechNerve.truncation.map_bijective f V :
  Function.Bijective (fun g : V ⟶ f.cechNerve ↦
    (SimplicialObject.truncation 1).map g))
#check (cechNerve.truncation.homEquiv f V :
  (V ⟶ f.cechNerve) ≃
    ((SimplicialObject.truncation 1).obj V ⟶
      (SimplicialObject.truncation 1).obj f.cechNerve))
#check cechNerve.truncation.homEquiv.apply f V
#check cechNerve.truncation.homEquiv.symm_apply f V

/- Lemma 14.20.3 (2): maps into the Cech nerve are classified by compatible degree-zero maps. -/
@[stacks 018I "Lemma 14.20.3 (2)"]
#check (cechNerve.zeroSimplex.homEquiv f V :
  (V ⟶ f.cechNerve) ≃
    cechNerve.CompatibleZeroSimplex f V)

/- The reusable classifier is packaged as an explicit representation, so later constructions can
use its Yoneda API without rebuilding the degree-zero equivalence. -/
@[stacks 018I "Lemma 14.20.3: representability companion"]
#check (cechNerve.zeroSimplex.representableBy f :
  (cechNerve.zeroSimplex.presheaf f).RepresentableBy f.cechNerve)
#check (cechNerve.zeroSimplex.yonedaIso (C := C))
#check cechNerve.zeroSimplex.yonedaIso_app

/- Lemma 14.20.3 (3): the Cech nerve is recovered from its `1`-truncation. -/
@[stacks 018I "Lemma 14.20.3 (3)"]
#check (cechNerve.isCoskeletalOne f : f.cechNerve.IsCoskeletal 1)

end CategoryTheory.Arrow
