module

import ReasLib.CategoryTheory.Sites.Sheaf.MorphismCriteria
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {F G : Sheaf J (Type w)} (φ : F ⟶ G)

/- Definition 7.11.1 (1) -/
@[stacks 00WM]
#check (CategoryTheory.Sheaf.isLocallyInjective_iff_objectwiseInjective φ :
  CategoryTheory.Sheaf.IsLocallyInjective φ ↔
    ∀ U : C, Function.Injective (φ.hom.app (op U)))

/- Definition 7.11.1 (2) -/
@[stacks 00WM]
#check (CategoryTheory.Sheaf.isLocallySurjective_iff_exists_coveringSieve φ :
  CategoryTheory.Sheaf.IsLocallySurjective φ ↔
    ∀ (U : C) (s : G.obj.obj (op U)),
      ∃ S : Sieve U, S ∈ J U ∧
        ∀ ⦃V : C⦄ (f : V ⟶ U), S f →
          ∃ t : F.obj.obj (op V),
            φ.hom.app (op V) t = G.obj.map f.op s)
