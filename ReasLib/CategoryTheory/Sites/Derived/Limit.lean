module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Grothendieck
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential derived limits of abelian sheaves

For an arbitrary site, the total right derived inverse limit of a derived inverse-system object
is a homotopy limit of its stagewise evaluations.  This site-specific result does not impose
exactness of countable products on the category of sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.AbelianSheaf

variable {C : Type u} [Category.{v} C]

namespace Sequential

/-- Sequential inverse systems of abelian sheaves carry their canonical standard derived
category. -/
@[stacks 0941 "derived category of sequential abelian sheaves"]
instance hasDerivedCategory (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}] :
    HasDerivedCategory
      (SequentialInverseSystem (Sheaf J AddCommGrpCat.{max u v})) :=
  HasDerivedCategory.standard _

end Sequential

namespace DerivedLimit

/-- Lemma 21.23.1 (0941): the derived inverse limit of an inverse-system object of abelian
sheaves is a derived limit of its stagewise evaluation tower. -/
@[stacks 0941 "stagewise derived limit of abelian sheaves"]
theorem isDerivedLimit_of_tower (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    (K : DerivedCategory
      (SequentialInverseSystem (Sheaf J AddCommGrpCat.{max u v}))) :
    Nonempty
      (IsDerivedLimit
        (CategoryTheory.DerivedLimit.Stage.tower K)
        ((CategoryTheory.DerivedLimit.functor
          (Sheaf J AddCommGrpCat.{max u v})).obj K)) := sorry

end DerivedLimit

end CategoryTheory.AbelianSheaf

end
