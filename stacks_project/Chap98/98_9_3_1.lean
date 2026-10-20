module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Lemma_98_9_3_FormalObject
public import stacks_project.Chap98.Definition_98_9_1_Hom
public import stacks_project.Chap98.«98_9_3_1_Approximation»
import StacksCheckRecall

/-!
# Approximation of objects by formal objects

Stacks tag 07X6: restricting an object of a category fibred in groupoids over
`(Sch/S)_fppf` along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)` yields a formal object, and
this construction is functorial.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/- 98.9.3.1: Approximation sends an object over a Noetherian complete local
`S`-algebra with residue field of finite type over `S` to its restrictions along
`Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. Stage `n` is the source stage `ξ_{n+1}`.
As authorized in source-issues/registry.json, key 07X6, the source category has
the indicated objects and only morphisms inducing local `S`-algebra maps;
this corrects the passage's full-subcategory assertion to a non-full subcategory. -/
@[stacks 07X6] #check (AlgebraicGeometry.GroupoidsOver.approximation :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S),
    CompleteLocalObject X ⥤ FormalObject X)

end AlgebraicGeometry.GroupoidsOver
