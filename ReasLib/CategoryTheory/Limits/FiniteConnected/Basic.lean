/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

universe w v₂ u₂ v₁ u₁ v u

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/-
A finite connected limit is intrinsically a limit over a finite connected shape. This is weaker
than `HasFiniteLimits`: nullary and disconnected shapes are deliberately excluded. As for
`HasFiniteLimits`, finite shapes can be resized, so the root owner stores only `Type`-small shapes
and the instance below transports it to every universe. The nLab construction by pullbacks and
equalizers is a characterization of this semantic owner, not its definition.
-/

/-- A category has finite connected limits if it has limits of every finite connected small
diagram. -/
@[stacks 04AT "finite connected limits"]
class HasFiniteConnectedLimits : Prop where
  /-- Every `Type`-small finite connected shape admits limits in the ambient category. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J] : HasLimitsOfShape J C

namespace HasFiniteConnectedLimits

/-- Finite connected limits supply limits for every finite connected small diagram, independently
of the universe of its shape. -/
@[stacks 04AT "finite connected limits of arbitrary shape"]
instance (priority := 90) hasLimitsOfShape [HasFiniteConnectedLimits C]
    (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J] : HasLimitsOfShape J C :=
  @hasLimitsOfShape_of_equivalence _ _ _ _ _ _ (FinCategory.equivAsType J)
    (@HasFiniteConnectedLimits.out C _ _ (FinCategory.AsType J) _ _
      (isConnected_of_equivalent (FinCategory.equivAsType J).symm))
/- Proof strategy: transfer the stored instance along `FinCategory.equivAsType J`; transport
connectedness across its inverse and apply `HasFiniteConnectedLimits.out` to
`FinCategory.AsType J`. -/

/-- Finite limits include finite connected limits. -/
@[stacks 04AT "finite limits imply finite connected limits"]
instance (priority := 100) ofFiniteLimits [HasFiniteLimits C] : HasFiniteConnectedLimits C :=
  ⟨fun J _ _ _ ↦ @HasFiniteLimits.out C _ _ J _ _⟩
/- Proof strategy: every finite connected shape is finite, so use the corresponding
`HasLimitsOfShape` instance supplied by `HasFiniteLimits C`. -/

/-- Construct finite connected limits by supplying them in any one universe. -/
theorem ofSize
    (h : ∀ (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J],
      HasLimitsOfShape J C) :
    HasFiniteConnectedLimits C := sorry
/- Proof strategy: apply `h` to `ULiftHom (ULift J)`, transport connectedness along
`ULiftHomULiftCategory.equiv J`, and transfer the resulting limit instance back to the stored
`Type`-small shape. -/

namespace Pullbacks

/-- Equalizers and pullbacks construct all finite connected limits. -/
theorem ofEqualizers [HasEqualizers C] [HasPullbacks C] :
    HasFiniteConnectedLimits C := sorry
/- Proof strategy: for a finite connected shape, order its objects along finite zigzags from a
root. Iterated pullbacks extend a compatible family along this spanning schedule; iterated
equalizers impose the remaining finitely many naturality relations. The resulting cone satisfies
`IsLimit` and hence supplies `HasLimitsOfShape`. -/

/-- A category has limits of every finite connected small diagram if and only if it has
equalizers and pullbacks. -/
@[stacks 04AT "finite connected limit criteria"]
theorem iff_equalizers :
    HasFiniteConnectedLimits C ↔ HasEqualizers C ∧ HasPullbacks C := sorry
/- Proof strategy: specialize `hasLimitsOfShape` to `WalkingParallelPair` and `WalkingCospan` in
the forward direction. For the reverse direction, install the two components and apply
`Pullbacks.ofEqualizers C`. -/

end Pullbacks

end HasFiniteConnectedLimits

/-
Finite connected colimits are a first-class dual owner. Encoding them permanently as
`HasFiniteConnectedLimits Cᵒᵖ` leaks an implementation device into every source-facing
statement; the explicit owner below keeps ordinary colimit APIs readable, while `iff_limits_op`
supplies the duality bridge when a proof needs it.
-/

/-- A category has finite connected colimits if it has colimits of every finite connected small
diagram. -/
@[stacks 04AV "finite connected colimits"]
class HasFiniteConnectedColimits : Prop where
  /-- Every `Type`-small finite connected shape admits colimits in the ambient category. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J] : HasColimitsOfShape J C

namespace HasFiniteConnectedColimits

/-- Finite connected colimits supply colimits for every finite connected small diagram,
independently of the universe of its shape. -/
@[stacks 04AV "finite connected colimits of arbitrary shape"]
instance (priority := 90) hasColimitsOfShape [HasFiniteConnectedColimits C]
    (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J] :
    HasColimitsOfShape J C :=
  @hasColimitsOfShape_of_equivalence _ _ _ _ _ _ (FinCategory.equivAsType J)
    (@HasFiniteConnectedColimits.out C _ _ (FinCategory.AsType J) _ _
      (isConnected_of_equivalent (FinCategory.equivAsType J).symm))
/- Proof strategy: transfer the stored instance along `FinCategory.equivAsType J`, transporting
connectedness across the inverse equivalence exactly as in the limit case. -/

/-- Finite colimits include finite connected colimits. -/
@[stacks 04AV "finite colimits imply finite connected colimits"]
instance (priority := 100) ofFiniteColimits [HasFiniteColimits C] :
    HasFiniteConnectedColimits C :=
  ⟨fun J _ _ _ ↦ @HasFiniteColimits.out C _ _ J _ _⟩
/- Proof strategy: every finite connected shape is finite, so use the corresponding
`HasColimitsOfShape` instance supplied by `HasFiniteColimits C`. -/

/-- Construct finite connected colimits by supplying them in any one universe. -/
theorem ofSize
    (h : ∀ (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J],
      HasColimitsOfShape J C) :
    HasFiniteConnectedColimits C := sorry
/- Proof strategy: apply `h` to `ULiftHom (ULift J)`, transport connectedness along the lifted
equivalence, and transfer the colimit instance back to the stored `Type`-small shape. -/

/-- Finite connected colimits in `C` are finite connected limits in `Cᵒᵖ`. -/
theorem iff_limits_op :
    HasFiniteConnectedColimits C ↔ HasFiniteConnectedLimits Cᵒᵖ := sorry
/- Proof strategy: replace each finite connected shape `J` by `Jᵒᵖ`; use the generic opposite
equivalences between `HasColimitsOfShape J C` and `HasLimitsOfShape Jᵒᵖ Cᵒᵖ`, noting that
finiteness and connectedness are preserved by opposite categories. -/

namespace Pushouts

/-- Coequalizers and pushouts construct all finite connected colimits. -/
theorem ofCoequalizers [HasCoequalizers C] [HasPushouts C] :
    HasFiniteConnectedColimits C := sorry
/- Proof strategy: dualize `HasFiniteConnectedLimits.Pullbacks.ofEqualizers` through
`iff_limits_op`. -/

/-- A category has all finite connected colimits if and only if it has coequalizers and
pushouts. -/
@[stacks 04AV "finite connected colimit criteria"]
theorem iff_coequalizers :
    HasFiniteConnectedColimits C ↔ HasCoequalizers C ∧ HasPushouts C := sorry

end Pushouts

/-- Finite connected colimits in `C` give finite connected limits in `Cᵒᵖ`. -/
theorem op [HasFiniteConnectedColimits C] : HasFiniteConnectedLimits Cᵒᵖ := sorry

/-- Finite connected colimits in `Cᵒᵖ` give finite connected limits in `C`. -/
theorem unop [HasFiniteConnectedColimits Cᵒᵖ] : HasFiniteConnectedLimits C := sorry

end HasFiniteConnectedColimits

namespace HasFiniteConnectedLimits

/-- Finite connected limits in `C` are finite connected colimits in `Cᵒᵖ`. -/
theorem iff_colimits_op :
    HasFiniteConnectedLimits C ↔ HasFiniteConnectedColimits Cᵒᵖ := sorry

/-- Finite connected limits in `C` give finite connected colimits in `Cᵒᵖ`. -/
theorem op [HasFiniteConnectedLimits C] : HasFiniteConnectedColimits Cᵒᵖ := sorry

/-- Finite connected limits in `Cᵒᵖ` give finite connected colimits in `C`. -/
theorem unop [HasFiniteConnectedLimits Cᵒᵖ] : HasFiniteConnectedColimits C := sorry

end HasFiniteConnectedLimits

end CategoryTheory.Limits


