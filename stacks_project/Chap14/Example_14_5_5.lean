/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.Cech.Conerve.LowDegree
import StacksCheckRecall

/-!
@stack 016N
-/

@[expose] public section

open CategoryTheory Limits
open scoped Simplicial

universe v u

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C] (f : Arrow C)
variable [f.HasCechConerve]

/- Example 14.5.5 (016N) (1): the Cech conerve of a morphism with the required iterated
pushouts. -/
@[stacks 016N "Example 14.5.5 (1)"]
#check (f.cechConerve : CosimplicialObject C)

#check (f.augmentedCechConerve : CosimplicialObject.Augmented C)

/- Example 14.5.5 (016N) (2): simplex operators reindex the components of the iterated
pushout. -/
@[stacks 016N "Example 14.5.5 (2)"]
#check (cechConerve.ι_map f :
  ∀ {n m : SimplexCategory} (α : n ⟶ m) (i : Fin (n.len + 1)),
    cechConerve.ι f n i ≫ f.cechConerve.map α =
      cechConerve.ι f m (α.toOrderHom i))

#check (cechConerve.head_map f :
  ∀ {n m : SimplexCategory} (α : n ⟶ m),
    cechConerve.head f n ≫ f.cechConerve.map α = cechConerve.head f m)

/- Example 14.5.5 (016N) (3): degree zero is canonically the target of the arrow. -/
@[stacks 016N "Example 14.5.5 (3)"]
#check (cechConerve.degreeZero.iso f :
  f.right ≅ f.cechConerve.obj ⦋0⦌)

/- Example 14.5.5 (016N) (4): degree one, with its two component coprojections, is the
pushout of the arrow along itself. -/
@[stacks 016N "Example 14.5.5 (4)"]
#check (cechConerve.degreeOne.isColimit f :
  IsColimit (cechConerve.degreeOne.cocone f))

/- Example 14.5.5 (016N) (5): the zeroth coface is the second coprojection. -/
@[stacks 016N "Example 14.5.5 (5)"]
#check (cechConerve.degreeOne.iso_hom_face_zero f :
  (cechConerve.degreeZero.iso f).hom ≫ f.cechConerve.δ (0 : Fin 2) =
    cechConerve.degreeOne.inr f)

/- Example 14.5.5 (016N) (6): the first coface is the first coprojection. -/
@[stacks 016N "Example 14.5.5 (6)"]
#check (cechConerve.degreeOne.iso_hom_face_one f :
  (cechConerve.degreeZero.iso f).hom ≫ f.cechConerve.δ (1 : Fin 2) =
    cechConerve.degreeOne.inl f)

/- The inverse degree-zero comparison recovers both cofaces from the pushout coprojections. -/
#check (cechConerve.degreeOne.iso_inv_inr f :
  (cechConerve.degreeZero.iso f).inv ≫ cechConerve.degreeOne.inr f =
    f.cechConerve.δ (0 : Fin 2))
#check (cechConerve.degreeOne.iso_inv_inl f :
  (cechConerve.degreeZero.iso f).inv ≫ cechConerve.degreeOne.inl f =
    f.cechConerve.δ (1 : Fin 2))

/- Example 14.5.5 (016N) (7): the degree-zero codegeneracy is the identity on the first
component. -/
@[stacks 016N "Example 14.5.5 (7)"]
#check (cechConerve.degreeOne.inl_codiagonal f :
  cechConerve.degreeOne.inl f ≫ cechConerve.degreeOne.codiagonal f = 𝟙 f.right)

/- Example 14.5.5 (016N) (8): the degree-zero codegeneracy is the identity on the second
component. -/
@[stacks 016N "Example 14.5.5 (8)"]
#check (cechConerve.degreeOne.inr_codiagonal f :
  cechConerve.degreeOne.inr f ≫ cechConerve.degreeOne.codiagonal f = 𝟙 f.right)

end CategoryTheory.Arrow
