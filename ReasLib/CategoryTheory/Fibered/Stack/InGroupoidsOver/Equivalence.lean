/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.OnHom
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.FullSubbicategory
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence data for morphisms of stacks in groupoids

`StackOver.Groupoids.Hom.IsEquivalence` is the property-level interface saying that the
underlying based functor is an equivalence over the base.  This file connects that predicate to
the bicategorical data owners `Bicategory.Equivalence` and `Bicategory.Equivalence.OnHom`.

The construction lifts the chosen based quasi-inverse through the two canonical full
subbicategories, first to groupoid-fibered categories and then to stacks.  Both lifts retain the
given forward morphism definitionally, so no equality transport or proof-local instance is
needed.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty

namespace StackOver.Groupoids.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Groupoids J}

/-- Lift an explicit proof that a stack morphism is an equivalence over the base to a
bicategorical equivalence of stacks.  The proof is an ordinary argument, so consumers do not
need to install a local `BasedFunctor.IsEquivalence` instance. -/
@[stacks 02ZK "lifted equivalence data for groupoid-stack morphisms"]
noncomputable def asEquivalenceOf {F : X ⟶ Y} (hF : IsEquivalence F) :
    X ≌ Y :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (ObjectProperty.FullSubbicategory.asEquivalenceOf F.hom hF)

/-- The forward morphism of `asEquivalenceOf hF` is the original stack morphism. -/
@[simp, stacks 02ZK "forward morphism of lifted groupoid-stack equivalence"]
theorem asEquivalenceOf.hom {F : X ⟶ Y} (hF : IsEquivalence F) :
    (asEquivalenceOf hF).hom = F := sorry

namespace IsEquivalence

/-- Chosen bicategorical equivalence data on a stack morphism known to be an equivalence over
the base.  The fixed-morphism owner avoids storing or transporting a second copy of `F`. -/
@[stacks 02ZK "fixed-morphism equivalence data for groupoid-stack morphisms"]
noncomputable def toOnHom {F : X ⟶ Y} (hF : IsEquivalence F) :
    Bicategory.Equivalence.OnHom F :=
  Bicategory.Equivalence.OnHom.ofEquivalence (asEquivalenceOf hF)

/-- Reassembling the fixed-morphism data selected by `toOnHom` recovers the canonical lifted
bicategorical equivalence. -/
@[simp, stacks 02ZK "equivalence reconstruction for groupoid-stack morphisms"]
theorem toOnHom.toEquivalence {F : X ⟶ Y} (hF : IsEquivalence F) :
    hF.toOnHom.toEquivalence = asEquivalenceOf hF := sorry

/-- Bicategorical equivalence data on a stack morphism imply that its underlying based functor
is an equivalence over the base. -/
@[stacks 02ZK "equivalence predicate readout for groupoid-stack morphisms"]
theorem ofOnHom {F : X ⟶ Y}
    (hF : Bicategory.Equivalence.OnHom F) :
    IsEquivalence F := sorry

end IsEquivalence

/- Data audit (mathlib 4.32): `asEquivalenceOf` selects the already encapsulated based
quasi-inverse and lifts it through two full subbicategories.  `IsEquivalence.toOnHom` only
restricts that bicategorical equivalence to its definitionally fixed forward morphism.  Neither
definition chooses another inverse, constructs an equality transport, or rebuilds an instance;
deferred content belongs to inherited triangle and full-subbicategory coherence fields. -/

end StackOver.Groupoids.Hom

end CategoryTheory
