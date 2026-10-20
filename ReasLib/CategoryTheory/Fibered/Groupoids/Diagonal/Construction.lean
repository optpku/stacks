/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Diagonal
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of groupoid-fibred diagonals

This leaf constructs the canonical diagonal into a self-`2`-fibre product on actual objects and
morphisms. Both projection isomorphisms have identity components; their walking-cospan
comparison is assembled from these same components. Computation theorems and equivalence
criteria are kept in sibling leaves.
-/

@[expose] public section

open CategoryTheory
open Bicategory
open scoped Pseudofunctor.StrongTrans

universe u v w

namespace CategoryTheory

namespace FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}

section

/-- The canonical diagonal morphism attached to a morphism of categories fibred in groupoids over
`C`. Its underlying functor sends `x` to `(x, x, id)` and a morphism `m` to `(m, m)` in the actual
self `2`-fibre product. -/
@[stacks 04Z7 "canonical diagonal morphism"]
noncomputable def Hom.diagonal (F : X ⟶ Y) :
    X ⟶ CategoryTheory.TwoFibreProduct.apex F F :=
  ofBasedFunctor
    { toFunctor :=
        { obj := fun x =>
            BasedCategory.PseudoPullback.mk F.hom F.hom (X.p.obj x)
              { fst := ⟨x, rfl⟩
                snd := ⟨x, rfl⟩
                iso := Iso.refl _ }
          map := fun m =>
            BasedCategory.PseudoPullback.Hom.mk (X.p.map m) m
              (Functor.IsHomLift.map m) m (Functor.IsHomLift.map m) sorry
          map_id := sorry
          map_comp := sorry }
      w := sorry }

namespace Hom.diagonal

/-- The first projection of the canonical diagonal is isomorphic to the identity of its source,
with the identity isomorphism on every object as component. -/
@[stacks 04Z7 "first projection of the canonical diagonal"]
noncomputable def fstIso (F : X ⟶ Y) :
    Hom.diagonal F ≫ CategoryTheory.TwoFibreProduct.fst F F ≅ 𝟙 X :=
  InducedBicategory.isoMk
    (BasedNatIso.ofComponents (fun _ => Iso.refl _) sorry sorry)

/-- The second projection of the canonical diagonal is isomorphic to the identity of its source,
with the identity isomorphism on every object as component. -/
@[stacks 04Z7 "second projection of the canonical diagonal"]
noncomputable def sndIso (F : X ⟶ Y) :
    Hom.diagonal F ≫ CategoryTheory.TwoFibreProduct.snd F F ≅ 𝟙 X :=
  InducedBicategory.isoMk
    (BasedNatIso.ofComponents (fun _ => Iso.refl _) sorry sorry)

/-- The walking-cospan comparison for `Hom.diagonal F`, assembled from actual identity
components at the central and two projection vertices. -/
@[stacks 04Z7 "universal comparison for the canonical diagonal"]
noncomputable def comparisonIso (F : X ⟶ Y) :
    ((CategoryTheory.TwoFibreProduct.cone F F).toPseudoCone.comparison X).obj
        (Hom.diagonal F) ≅
      (PseudoPullbackCone.diagonal F).toPseudoCone.π :=
  Pseudofunctor.StrongTrans.isoMk
    (fun a => match a with
      | ⟨none⟩ => InducedBicategory.isoMk
          (BasedNatIso.ofComponents (fun _ => Iso.refl _) sorry sorry)
      | ⟨some Limits.WalkingPair.left⟩ => fstIso F
      | ⟨some Limits.WalkingPair.right⟩ => sndIso F)
    sorry

end Hom.diagonal

/-- The object-level diagonal specialization for a bundled groupoid-fibred category. -/
@[stacks 02YA "diagonal of a category fibred in groupoids"]
noncomputable abbrev diagonal
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) :
    X ⟶ CategoryTheory.TwoFibreProduct.apex X.baseProjection X.baseProjection :=
  Hom.diagonal X.baseProjection

end

end FiberedCategoryOver.Groupoids

end CategoryTheory
