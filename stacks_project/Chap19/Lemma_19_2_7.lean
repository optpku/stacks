/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Injective.Baer.Functorial
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace ModuleCat

variable (R : Type u) [Ring R]

/- Lemma 19.2.7 (1): `M ↦ Baer.step R M` is functorial and the canonical maps into the
Baer steps form a natural transformation. -/
@[stacks 05NW "(1)"] #check
  (Baer.inclusionNatTrans.{0, u} R :
    𝟭 (ModuleCat.{u} R) ⟶ Baer.stepFunctor.{0, u} R)

/- Lemma 19.2.7 (2): every canonical map into a Baer step is injective. -/
@[stacks 05NW "(2)"] #check
  fun M : ModuleCat.{u} R ↦
    (Baer.inclusion_injective.{0, u} R M :
      Function.Injective (Baer.inclusion.{0, u} R M).hom)

/- Lemma 19.2.7 (3): every map from an ideal to `M` extends to a map from `R` into the Baer
step, compatibly with the canonical inclusion of `M`. -/
@[stacks 05NW "(3)"] #check
  fun (M : ModuleCat.{u} R) (I : Ideal R) (φ : ModuleCat.of R I ⟶ M) ↦
    (Baer.idealLift_commSq R M I φ :
      CommSq (ModuleCat.ofHom I.subtype) φ
        (Baer.idealLift R M I φ) (Baer.inclusion.{0, u} R M))

end ModuleCat
