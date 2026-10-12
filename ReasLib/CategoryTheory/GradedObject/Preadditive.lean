/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.GradedObject.Instances
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive Graded Objects

Mathlib's pointwise zero morphisms on graded objects are the canonical presentation, including
when the ambient category is preadditive.  This module deliberately introduces no competing
zero-morphism instance: doing so breaks definitional equality for homological-complex data built
before the preadditive structure is inferred.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.GradedObject

variable {β : Type w} {C : Type u} [Category.{v} C]

/- In a preadditive ambient category, retain the existing pointwise `GradedObject.hasZeroMorphisms`
instance rather than installing the structurally distinct zero morphisms induced by `Preadditive`.
The former is the canonical owner used by graded objects and homological complexes throughout
mathlib. -/

end CategoryTheory.GradedObject
