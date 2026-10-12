/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.GradedObject.Homology
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/- Lemma 12.16.2: integer-graded objects in an abelian category form an abelian category. -/
@[stacks 0126] #check (inferInstance : Abelian (GradedObject ℤ 𝒜))

/- The shared instance is grading-type independent. -/
variable (β : Type w)
#check (inferInstance : Abelian (GradedObject β 𝒜))

/- Consequently the standard homology package is available without a chapter-local instance. -/
#check (inferInstance : CategoryWithHomology (GradedObject β 𝒜))

end CategoryTheory
