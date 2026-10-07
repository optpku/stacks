module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Diagonal
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of groupoid-fibred diagonals

This leaf owns the universal-lift data for the canonical diagonal into a self-`2`-fibre product,
including its comparison and projection isomorphisms.  Computation theorems and equivalence
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
`C`, obtained by universally lifting `PseudoPullbackCone.diagonal F` to the canonical self
`2`-fibre product. -/
@[stacks 04Z7 "canonical diagonal morphism"]
noncomputable def Hom.diagonal (F : X ⟶ Y) :
    X ⟶ CategoryTheory.TwoFibreProduct.apex F F :=
  PseudoPullbackCone.lift
    (PseudoPullbackCone.diagonal F) (CategoryTheory.TwoFibreProduct.cone F F)

namespace Hom.diagonal

/-- The universal-property comparison for `Hom.diagonal F`. -/
@[stacks 04Z7 "universal comparison for the canonical diagonal"]
noncomputable def comparisonIso (F : X ⟶ Y) :
    ((CategoryTheory.TwoFibreProduct.cone F F).toPseudoCone.comparison X).obj
        (Hom.diagonal F) ≅
      (PseudoPullbackCone.diagonal F).toPseudoCone.π :=
  PseudoPullbackCone.lift.comparisonIso
    (PseudoPullbackCone.diagonal F) (CategoryTheory.TwoFibreProduct.cone F F)

/-- The first projection of the canonical diagonal is isomorphic to the identity of its source. -/
@[stacks 04Z7 "first projection of the canonical diagonal"]
noncomputable def fstIso (F : X ⟶ Y) :
    Hom.diagonal F ≫ CategoryTheory.TwoFibreProduct.fst F F ≅ 𝟙 X :=
  PseudoPullbackCone.lift.fstIso
    (PseudoPullbackCone.diagonal F) (CategoryTheory.TwoFibreProduct.cone F F)

/-- The second projection of the canonical diagonal is isomorphic to the identity of its source. -/
@[stacks 04Z7 "second projection of the canonical diagonal"]
noncomputable def sndIso (F : X ⟶ Y) :
    Hom.diagonal F ≫ CategoryTheory.TwoFibreProduct.snd F F ≅ 𝟙 X :=
  PseudoPullbackCone.lift.sndIso
    (PseudoPullbackCone.diagonal F) (CategoryTheory.TwoFibreProduct.cone F F)

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
