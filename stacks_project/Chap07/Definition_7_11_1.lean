module

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {F G : Sheaf J (Type w)} (φ : F ⟶ G)

/-
Definition 7.11.1 (1): a map φ : F ⟶ G of sheaves of sets on a site C is injective if
for every object U of C the component φ.hom.app (op U) is Function.Injective.
This is the sheaf morphism class Sheaf.IsLocallyInjective, which for sheaves is
objectwise injectivity by isLocallyInjective_iff_injective.
-/
@[stacks 00WM "(1)"]
#check (Sheaf.IsLocallyInjective φ)

#check @CategoryTheory.Sheaf.isLocallyInjective_iff_injective

/-
Definition 7.11.1 (2): a map φ : F ⟶ G of sheaves of sets on a site C is surjective if
for every object U of C and every section s of G at U there exists a covering
{Uᵢ ⟶ U} such that each restriction of s along Uᵢ is in the image of
φ.hom.app (op Uᵢ). This is the sheaf morphism class Sheaf.IsLocallySurjective,
whose covering-local image condition is membership of Presheaf.imageSieve φ.hom s
in the Grothendieck topology J.
-/
@[stacks 00WM "(2)"]
#check (Sheaf.IsLocallySurjective φ)

#check @CategoryTheory.Presheaf.imageSieve
#check @CategoryTheory.Presheaf.imageSieve_mem
