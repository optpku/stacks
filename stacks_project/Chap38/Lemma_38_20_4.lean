/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.LocalAlgebra.Flattening.Preservation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace LocalAlgCat.Flattening

variable (A : Type u) (B : Type v) (M : Type w)
variable [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [AddCommGroup M] [Module B M]

/- Lemma 38.20.4 (1): a flat morphism of local `A`-algebras induces a bijection between
the corresponding fibers of the flattening functor. -/
@[stacks 05MN]
#check
  (LocalAlgCat.Flattening.map_bijective_of_flat A B M :
    ∀ {T U : LocalAlgCat.{v} A} (f : T ⟶ U),
      (LocalAlgCat.Hom.toLocal A f).hom.toRingHom.Flat →
        Function.Bijective ((LocalAlgCat.Flattening.functor A B M).map f))

variable [Algebra.EssFinitePresentation A B] [Module.FinitePresentation B M]

/- Lemma 38.20.4 (2): if `A → B` is essentially of finite presentation and `M` is a
finitely presented `B`-module, then the flattening functor preserves filtered colimits. -/
@[stacks 05MN]
#check
  (LocalAlgCat.Flattening.preservesFilteredColimits A B M :
    PreservesFilteredColimits (LocalAlgCat.Flattening.functor A B M))

end LocalAlgCat.Flattening
