/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Graph.Equivalence
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Graph equivalences for explicit two-fibre products

The identity-leg graph and its canonical equivalence. The equivalence coherence is inherited
from the ambient graph equivalence through the generic full-subbicategory lift.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]
variable {X Y : P.FullSubbicategory}

/-- The graph of a morphism into its explicit two-fibre product with the identity. This is the
fixed-bicategory owner of the ambient heterogeneous-universe graph construction. -/
@[stacks 0040 "graph into a full-subbicategory two-fibre product with an identity leg"]
def graph (F : X ⟶ Y) : X ⟶ apex F (𝟙 Y) :=
  Bicategory.InducedBicategory.mkHom
    (BasedCategory.PseudoPullback.graph F.hom)

/-- Forgetting the owner-level graph recovers the explicit based pseudo-pullback graph. -/
@[simp]
theorem graph.hom (F : X ⟶ Y) :
    (graph F).hom = BasedCategory.PseudoPullback.graph F.hom := sorry

/-- The first projection of the owner-level graph is the identity. -/
@[simp]
theorem graph.fst (F : X ⟶ Y) :
    graph F ≫ fst F (𝟙 Y) = 𝟙 X := sorry

/-- The second projection of the owner-level graph is the original morphism. -/
@[simp]
theorem graph.snd (F : X ⟶ Y) :
    graph F ≫ snd F (𝟙 Y) = F := sorry

/-- The canonical equivalence from an object to its full-subbicategory two-fibre product with
an identity leg. Its inverse, unit, counit, and triangle data are inherited from the ambient
graph equivalence by the generic full-subbicategory lift. -/
@[stacks 0040 "graph equivalence in a full-subbicategory two-fibre product"]
noncomputable def graph.equivalence (F : X ⟶ Y) : X ≌ apex F (𝟙 Y) :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (BasedCategory.PseudoPullback.graph.equivalence F.hom)

/-- The forward `1`-morphism of the canonical graph equivalence is the graph. -/
@[simp]
theorem graph.equivalence.hom (F : X ⟶ Y) :
    (graph.equivalence F).hom = graph F := sorry

/-- The inverse `1`-morphism of the canonical graph equivalence is the first projection. -/
@[simp]
theorem graph.equivalence.inv (F : X ⟶ Y) :
    (graph.equivalence F).inv =
      TwoFibreProduct.fst F (𝟙 Y) := sorry

/- Data audit: `graph.equivalence` delegates all non-`Prop` inverse and coherence data to
`BasedCategory.PseudoPullback.graph.equivalence` and changes only the bicategorical owner via
`ObjectProperty.FullSubbicategory.equivalenceOfAmbient`. -/

end TwoFibreProduct

end CategoryTheory
