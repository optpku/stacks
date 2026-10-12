/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.GradedObject.Instances
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped CategoryTheory

universe v u

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜]

/- Definition 12.16.1: `Gr(𝒜)` is the canonical category `GradedObject ℤ 𝒜` of integer-indexed
families in the additive category `𝒜`. -/
@[stacks 0125] #check Gr(𝒜)

variable {𝒜} (A B : Gr(𝒜)) (i : ℤ)

/- Morphisms of graded objects are evaluated componentwise. -/
#check (fun (f : A ⟶ B) => f i : (A ⟶ B) → (A i ⟶ B i))

/- The reusable component projection is the canonical evaluation functor. -/
#check (GradedObject.eval i : Gr(𝒜) ⥤ 𝒜)

end CategoryTheory
