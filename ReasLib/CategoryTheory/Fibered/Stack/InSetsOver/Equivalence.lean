module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.OnHom
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence data for morphisms of stacks in sets

An equivalence over the base between stacks in sets is packaged at the stack-in-setoids layer and
lifted through the full subbicategory selecting discrete fibers. This retains the lower-layer
inverse, unit, and counit without selecting new data.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

namespace StackOver.Sets.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Sets J}

/-- Package equivalence of the underlying based functor as a bicategorical equivalence of
stacks in sets. -/
@[stacks 02ZK "set-stack lifted equivalence data"]
noncomputable def asEquivalenceOf {F : X ⟶ Y} (hF : IsEquivalence F) : X ≌ Y :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (StackOver.Setoids.Hom.asEquivalenceOf
      ((isEquivalence_iff_toSetoidsMor F).mp hF))

/-- The forward morphism of `asEquivalenceOf hF` is the original morphism of stacks in sets. -/
@[simp, stacks 02ZK "set-stack lifted equivalence forward readout"]
theorem asEquivalenceOf.hom {F : X ⟶ Y} (hF : IsEquivalence F) :
    (asEquivalenceOf hF).hom = F := sorry

namespace IsEquivalence

/-- Fixed-forward-morphism equivalence data for a morphism of stacks in sets. -/
@[stacks 02ZK "set-stack fixed-morphism equivalence data"]
noncomputable def toOnHom {F : X ⟶ Y} (hF : IsEquivalence F) :
    Bicategory.Equivalence.OnHom F :=
  Bicategory.Equivalence.OnHom.ofEquivalence (asEquivalenceOf hF)

/-- Reassembling the fixed-forward-morphism data gives the canonical lifted equivalence. -/
@[simp, stacks 02ZK "set-stack equivalence reconstruction"]
theorem toOnHom.toEquivalence {F : X ⟶ Y} (hF : IsEquivalence F) :
    hF.toOnHom.toEquivalence = asEquivalenceOf hF := sorry

/-- Bicategorical equivalence data on a morphism of stacks in sets imply equivalence of its
underlying based functor. -/
@[stacks 02ZK "set-stack equivalence predicate readout"]
theorem ofOnHom {F : X ⟶ Y} (hF : Bicategory.Equivalence.OnHom F) :
    IsEquivalence F := sorry

end IsEquivalence

/- Data audit: the stack-in-setoids owner supplies the inverse, unit, and counit;
`equivalenceOfAmbient` only retains them in the full subbicategory selected by the discrete-fiber
property. Deferred content is confined to property and bicategorical coherence proofs. -/

end StackOver.Sets.Hom

end CategoryTheory
