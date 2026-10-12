/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Setoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Thin
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-fibre products of stacks in setoids

This leaf owns the explicit setoid-valued carrier and its bilimit cone. The underlying groupoid
two-fibre product remains the canonical data owner; the only additional datum here is the
setoid-fiber proof.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Setoids.TwoFibreProduct

variable {X Y S :
  StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J}

/-- The ambient groupoid-fibred carrier underlying the setoid two-fibre product. -/
@[stacks 0434 "setoid-stack two-fibre-product ambient carrier"]
noncomputable abbrev ambient
    (F : X ⟶ S) (G : Y ⟶ S) :
    StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J :=
  StackOver.Groupoids.TwoFibreProduct.apex.{u, v, w, vB}
    (StackOver.Setoids.Hom.toGroupoidsMor F)
    (StackOver.Setoids.Hom.toGroupoidsMor G)

/-- The ambient carrier of a setoid two-fibre product has thin fibers. -/
@[stacks 0434 "setoid-stack two-fibre-product closure"]
theorem isFiberedInSetoids
    (F : X ⟶ S) (G : Y ⟶ S) :
    Functor.IsFibered.InSetoids (ambient F G).p := sorry

/-- The canonical stack in setoids carried by the ambient two-fibre product. -/
@[stacks 0434 "setoid-stack two-fibre-product apex"]
noncomputable abbrev apex
    (F : X ⟶ S) (G : Y ⟶ S) : StackOver.Setoids J :=
  ObjectProperty.FullSubbicategory.mk _ (ambient F G) (isFiberedInSetoids F G)

/-- Forgetting thinness from the setoid-stack apex recovers its groupoid-stack owner. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product apex groupoid readout"]
theorem apex.toGroupoids (F : X ⟶ S) (G : Y ⟶ S) :
    (apex F G).toGroupoids = ambient F G := sorry

/-- Forgetting directly to categories fibred in setoids recovers the neutral selected
two-fibre-product apex. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product apex setoid readout"]
theorem apex.toSetoids (F : X ⟶ S) (G : Y ⟶ S) :
    (apex F G).toSetoids =
      _root_.CategoryTheory.TwoFibreProduct.apex
        (StackOver.Setoids.Hom.toSetoidsMor F)
        (StackOver.Setoids.Hom.toSetoidsMor G) := sorry

/-- The left projection of the setoid two-fibre product. -/
@[stacks 0434 "setoid-stack two-fibre-product first projection"]
noncomputable abbrev fst
    (F : X ⟶ S) (G : Y ⟶ S) : apex F G ⟶ X :=
  StackOver.Setoids.Hom.lift
    (StackOver.Groupoids.TwoFibreProduct.fst
      (StackOver.Setoids.Hom.toGroupoidsMor F)
      (StackOver.Setoids.Hom.toGroupoidsMor G))

/-- Forgetting thinness from the left projection recovers the groupoid-stack projection. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product first projection groupoid readout"]
theorem fst.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (fst F G).hom =
      StackOver.Groupoids.TwoFibreProduct.fst
        (StackOver.Setoids.Hom.toGroupoidsMor F)
        (StackOver.Setoids.Hom.toGroupoidsMor G) := sorry

/-- The setoid-fibred morphism underlying the left projection is the neutral projection;
heterogeneous equality accounts only for proof-bearing endpoints. -/
@[stacks 0434 "setoid-stack two-fibre-product first projection setoid readout"]
theorem fst.toSetoidsMor (F : X ⟶ S) (G : Y ⟶ S) :
    StackOver.Setoids.Hom.toSetoidsMor (fst F G) ≍
      _root_.CategoryTheory.TwoFibreProduct.fst
        (StackOver.Setoids.Hom.toSetoidsMor F)
        (StackOver.Setoids.Hom.toSetoidsMor G) := sorry

/-- The right projection of the setoid two-fibre product. -/
@[stacks 0434 "setoid-stack two-fibre-product second projection"]
noncomputable abbrev snd
    (F : X ⟶ S) (G : Y ⟶ S) : apex F G ⟶ Y :=
  StackOver.Setoids.Hom.lift
    (StackOver.Groupoids.TwoFibreProduct.snd
      (StackOver.Setoids.Hom.toGroupoidsMor F)
      (StackOver.Setoids.Hom.toGroupoidsMor G))

/-- Forgetting thinness from the right projection recovers the groupoid-stack projection. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product second projection groupoid readout"]
theorem snd.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (snd F G).hom =
      StackOver.Groupoids.TwoFibreProduct.snd
        (StackOver.Setoids.Hom.toGroupoidsMor F)
        (StackOver.Setoids.Hom.toGroupoidsMor G) := sorry

/-- The setoid-fibred morphism underlying the right projection is the neutral projection;
heterogeneous equality accounts only for proof-bearing endpoints. -/
@[stacks 0434 "setoid-stack two-fibre-product second projection setoid readout"]
theorem snd.toSetoidsMor (F : X ⟶ S) (G : Y ⟶ S) :
    StackOver.Setoids.Hom.toSetoidsMor (snd F G) ≍
      _root_.CategoryTheory.TwoFibreProduct.snd
        (StackOver.Setoids.Hom.toSetoidsMor F)
        (StackOver.Setoids.Hom.toSetoidsMor G) := sorry

/-- The canonical comparison isomorphism between the two projection composites
of the setoid-valued stack two-fibre product. -/
@[stacks 0434 "setoid-stack two-fibre-product comparison"]
noncomputable abbrev comparisonIso
    (F : X ⟶ S) (G : Y ⟶ S) :
    fst F G ≫ F ≅ snd F G ≫ G :=
  Bicategory.InducedBicategory.isoMk
    (StackOver.Groupoids.TwoFibreProduct.comparisonIso
      (StackOver.Setoids.Hom.toGroupoidsMor F)
      (StackOver.Setoids.Hom.toGroupoidsMor G))

/-- Forgetting thinness from the forward comparison cell recovers the groupoid-stack
comparison cell; heterogeneous equality accounts only for proof-bearing endpoints. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product comparison forward readout"]
theorem comparisonIso.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (comparisonIso F G).hom.hom ≍
      (StackOver.Groupoids.TwoFibreProduct.comparisonIso
        (StackOver.Setoids.Hom.toGroupoidsMor F)
        (StackOver.Setoids.Hom.toGroupoidsMor G)).hom := sorry

/-- Forgetting thinness from the inverse comparison cell recovers the inverse groupoid-stack
comparison cell; heterogeneous equality accounts only for proof-bearing endpoints. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product comparison inverse readout"]
theorem comparisonIso.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (comparisonIso F G).inv.hom ≍
      (StackOver.Groupoids.TwoFibreProduct.comparisonIso
        (StackOver.Setoids.Hom.toGroupoidsMor F)
        (StackOver.Setoids.Hom.toGroupoidsMor G)).inv := sorry

/-- The canonical pseudopullback cone of stacks in setoids. -/
@[stacks 0434 "setoid-stack two-fibre-product cone"]
noncomputable abbrev cone
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.PseudoPullbackCone F G :=
  Bicategory.PseudoPullbackCone.inFull
    (IsStack.InSetoids.objectProperty J)
    (StackOver.Groupoids.TwoFibreProduct.cone
      (StackOver.Setoids.Hom.toGroupoidsMor F)
      (StackOver.Setoids.Hom.toGroupoidsMor G))
    (isFiberedInSetoids F G)

/-- The apex of the canonical setoid-valued stack cone is the explicit
two-fibre product. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product cone apex readout"]
theorem cone.pt (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).pt = apex F G := sorry

/-- The first leg of the canonical setoid-valued stack cone is its first
projection. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product cone first leg readout"]
theorem cone.fst (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).fst = fst F G := sorry

/-- The second leg of the canonical setoid-valued stack cone is its second
projection. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product cone second leg readout"]
theorem cone.snd (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).snd = snd F G := sorry

/-- The structural cell of the canonical setoid-valued stack cone is its
comparison isomorphism. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product cone comparison readout"]
theorem cone.iso (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).iso = comparisonIso F G := sorry

/-- The setoid two-fibre-product cone is a bilimit. -/
@[stacks 0434 "standard pseudo-pullback description"]
instance cone.isBilimit
    (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).IsBilimit := sorry

/- The non-`Prop` fields below are inherited from the explicit groupoid two-fibre-product owner;
`sorryAx` in the audit is confined to its membership, stack, and coherence proofs. -/

end StackOver.Setoids.TwoFibreProduct

namespace StackOver.Setoids

/-- The bicategory of stacks in setoids over a site has pseudopullbacks. -/
@[stacks 0434 "two-fibre products of stacks in setoids"]
instance hasPseudoPullbacks : Bicategory.HasPseudoPullbacks (StackOver.Setoids J) := sorry

end StackOver.Setoids

end CategoryTheory
