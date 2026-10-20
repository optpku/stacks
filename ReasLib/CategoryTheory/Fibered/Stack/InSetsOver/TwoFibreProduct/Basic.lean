module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.TwoFibreProduct.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Discrete
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-fibre products of stacks in sets

The carrier is the explicit two-fibre product of the underlying stacks in setoids. The only new
datum is the strict discrete-fibration proof; neutral set-fibred readouts identify the construction
with the property-selected based pseudo-pullback.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Sets.TwoFibreProduct

variable {X Y S :
  StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J}

/-- The ambient setoid-stack carrier underlying the two-fibre product of stacks in sets. -/
@[stacks 0434 "set-stack two-fibre-product ambient carrier"]
noncomputable def ambient (F : X ⟶ S) (G : Y ⟶ S) :
    StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J :=
  StackOver.Setoids.TwoFibreProduct.apex
    (StackOver.Sets.Hom.toSetoidsMor F)
    (StackOver.Sets.Hom.toSetoidsMor G)

/-- The ambient set-stack two-fibre product has a discrete projection to the site. The canonical
closure is inherited from the neutral groupoid two-fibre-product owner; this instance is the
bundled set-stack specialization used by the constructor below. -/
@[stacks 0047 "set-stack two-fibre-product discrete-fibration closure"]
instance isDiscreteFibration (F : X ⟶ S) (G : Y ⟶ S) :
    Functor.IsDiscreteFibration (ambient F G).p := sorry

/-- Source-facing name for the discrete-fibration closure of the set-stack two-fibre product. -/
@[stacks 0434 "set-stack two-fibre-product closure"]
theorem isFiberedInSets (F : X ⟶ S) (G : Y ⟶ S) :
    Functor.IsDiscreteFibration (ambient F G).p := sorry

/-- The canonical stack in sets carried by the explicit ambient two-fibre product. -/
@[stacks 0434 "set-stack two-fibre-product apex"]
noncomputable def apex (F : X ⟶ S) (G : Y ⟶ S) : StackOver.Sets J :=
  ObjectProperty.FullSubbicategory.mk
    (IsStack.InSets.objectProperty J) (ambient F G) (isFiberedInSets F G)

/-- The first projection from the two-fibre product of stacks in sets. -/
@[stacks 0434 "set-stack two-fibre-product first projection"]
noncomputable def fst (F : X ⟶ S) (G : Y ⟶ S) : apex F G ⟶ X :=
  StackOver.Sets.Hom.lift
    (StackOver.Setoids.TwoFibreProduct.fst
      (StackOver.Sets.Hom.toSetoidsMor F)
      (StackOver.Sets.Hom.toSetoidsMor G))

/-- The second projection from the two-fibre product of stacks in sets. -/
@[stacks 0434 "set-stack two-fibre-product second projection"]
noncomputable def snd (F : X ⟶ S) (G : Y ⟶ S) : apex F G ⟶ Y :=
  StackOver.Sets.Hom.lift
    (StackOver.Setoids.TwoFibreProduct.snd
      (StackOver.Sets.Hom.toSetoidsMor F)
      (StackOver.Sets.Hom.toSetoidsMor G))

/-- The canonical comparison isomorphism between the two projection composites of the
set-valued stack two-fibre product. -/
@[stacks 0434 "set-stack two-fibre-product comparison"]
noncomputable def comparisonIso (F : X ⟶ S) (G : Y ⟶ S) :
    fst F G ≫ F ≅ snd F G ≫ G :=
  Bicategory.InducedBicategory.isoMk
    (StackOver.Setoids.TwoFibreProduct.comparisonIso
      (StackOver.Sets.Hom.toSetoidsMor F)
      (StackOver.Sets.Hom.toSetoidsMor G))

/-- The canonical pseudo-pullback cone of stacks in sets. -/
@[stacks 0434 "set-stack two-fibre-product cone"]
noncomputable def cone (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.PseudoPullbackCone F G :=
  Bicategory.PseudoPullbackCone.inFull
    (IsStack.InSets.objectProperty J)
    (StackOver.Setoids.TwoFibreProduct.cone
      (StackOver.Sets.Hom.toSetoidsMor F)
      (StackOver.Sets.Hom.toSetoidsMor G))
    (isFiberedInSets F G)

end StackOver.Sets.TwoFibreProduct

end CategoryTheory

/- The carrier, apex, projections, and cone retain the existing explicit setoid-stack and based
pseudo-pullback data. Any `sorryAx` is confined to discrete-fibration, stack, and bilimit proofs. -/
