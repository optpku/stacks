/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.LocalProperties
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Lift
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor

/-!
# Factorization API for locally induced bicategories

The canonical inclusions and strict lifts form strict factorizations after
forgetting their proof-valued hom-property witnesses.  This leaf packages those
factorizations and the local fully-faithful facts needed to transport `2`-cell
arguments without unfolding strict pseudofunctor structures.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u u' w' v' u''

namespace Bicategory

variable {B : Type u'}

namespace LocallyInducedBicategory

variable {C : Type u} [Bicategory.{w, v} C] {F : B → C}
  {Q : HomProperty F} [Q.IsMultiplicative]

section Inclusion

/-- The canonical inclusion into the induced bicategory is locally full. -/
instance ι.mapFunctor.full (X Y : LocallyInducedBicategory C F Q) :
    ((ι C F Q).mapFunctor X Y).Full := sorry

/-- The canonical inclusion into the induced bicategory is locally faithful. -/
instance ι.mapFunctor.faithful (X Y : LocallyInducedBicategory C F Q) :
    ((ι C F Q).mapFunctor X Y).Faithful := sorry

/-- The canonical inclusion into the induced bicategory is locally fully faithful. -/
@[stacks 0040 "local full faithfulness of the canonical inclusion"]
instance ι.isLocallyFullyFaithful :
    (ι C F Q).toPseudofunctor.IsLocallyFullyFaithful := sorry

end Inclusion

section Lift

variable {A : Type u''} [Bicategory.{w', v'} A]

/-- Forgetting the hom-property witnesses from a strict lift recovers the original strict
pseudofunctor as a pseudofunctor. -/
@[stacks 0040 "strict locally induced lift factorization"]
theorem lift.comp_ι (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom) :
    (lift G map_mem).toPseudofunctor.comp
        (ι C F Q).toPseudofunctor =
      G.toPseudofunctor := sorry

/-- Forgetting the hom-property witnesses from a pseudofunctor lift recovers
the original pseudofunctor. -/
@[stacks 0040 "locally induced pseudofunctor lift factorization"]
theorem liftPseudofunctor.comp_ι
    (G : Pseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom) :
    (liftPseudofunctor G map_mem).comp (ι C F Q).toPseudofunctor = G := sorry

end Lift

section PropertyInclusion

variable {R : HomProperty F} [R.IsMultiplicative]

/-- An inclusion induced by `Q ≤ R` is locally full. -/
instance ιOfLE.mapFunctor.full
    (h : Q ≤ R) (X Y : LocallyInducedBicategory C F Q) :
    ((ιOfLE h).mapFunctor X Y).Full := sorry

/-- An inclusion induced by `Q ≤ R` is locally faithful. -/
instance ιOfLE.mapFunctor.faithful
    (h : Q ≤ R) (X Y : LocallyInducedBicategory C F Q) :
    ((ιOfLE h).mapFunctor X Y).Faithful := sorry

/-- An inclusion induced by `Q ≤ R` is locally fully faithful. -/
@[stacks 0040 "local full faithfulness of a hom-property inclusion"]
instance ιOfLE.isLocallyFullyFaithful (h : Q ≤ R) :
    (ιOfLE h).toPseudofunctor.IsLocallyFullyFaithful := sorry

/-- Inclusion through `R` and then into the ambient induced bicategory equals the direct
inclusion through `Q`. -/
theorem ιOfLE.comp_ι (h : Q ≤ R) :
    (ιOfLE h).toPseudofunctor.comp
        (ι C F R).toPseudofunctor =
      (ι C F Q).toPseudofunctor := sorry

/-- Inclusion along a reflexive hom-property implication is the identity pseudofunctor. -/
theorem ιOfLE.eq_id (h : Q ≤ Q) :
    (ιOfLE h).toPseudofunctor =
      (StrictPseudofunctor.id (LocallyInducedBicategory C F Q)).toPseudofunctor := sorry

variable {S : HomProperty F} [S.IsMultiplicative]

/-- Successive inclusions along hom-property implications agree with their composite implication. -/
theorem ιOfLE.comp (hQR : Q ≤ R) (hRS : R ≤ S) :
    (ιOfLE hQR).toPseudofunctor.comp (ιOfLE hRS).toPseudofunctor =
      (ιOfLE (hQR.trans hRS)).toPseudofunctor := sorry

end PropertyInclusion

section Forget

/-- The canonical inclusion into the ambient bicategory is locally full. -/
instance forget.mapFunctor.full (X Y : LocallyInducedBicategory C F Q) :
    ((forget C F Q).mapFunctor X Y).Full := sorry
/- Proof strategy: identify the hom functor with the full-subcategory inclusion
`(Q X Y).ι`, then use `(Q X Y).fullyFaithfulι.full`. -/

/-- The canonical inclusion into the ambient bicategory is locally faithful. -/
instance forget.mapFunctor.faithful (X Y : LocallyInducedBicategory C F Q) :
    ((forget C F Q).mapFunctor X Y).Faithful := sorry
/- Proof strategy: identify the hom functor with `(Q X Y).ι`, then use
`(Q X Y).fullyFaithfulι.faithful`. -/

/-- Ambient forgetting from a locally induced bicategory is locally fully
faithful. -/
@[stacks 0040 "local full faithfulness of ambient forgetting"]
instance forget.isLocallyFullyFaithful :
    (forget C F Q : StrictPseudofunctor
      (LocallyInducedBicategory C F Q) C).toPseudofunctor.IsLocallyFullyFaithful := sorry
/- Proof strategy: supply `forget.mapFunctor.full X Y` and
`forget.mapFunctor.faithful X Y` at each pair of objects. -/

/-- The ambient forgetful pseudofunctor factors through the induced-bicategory inclusion. -/
theorem forget.eq_ι_comp :
    (forget C F Q).toPseudofunctor =
      (ι C F Q).toPseudofunctor.comp
        (InducedBicategory.forget (C := C) (F := F)).toPseudofunctor := sorry

variable {R : HomProperty F} [R.IsMultiplicative]

/-- Forgetting after a hom-property inclusion agrees with forgetting directly. -/
theorem ιOfLE.comp_forget (h : Q ≤ R) :
    (ιOfLE h).toPseudofunctor.comp
        (forget C F R).toPseudofunctor =
      (forget C F Q).toPseudofunctor := sorry

end Forget

end LocallyInducedBicategory

end Bicategory

end CategoryTheory
