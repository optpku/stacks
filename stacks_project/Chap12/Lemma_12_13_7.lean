module

public import ReasLib.Algebra.Homology.Homotopy.Whisker
import StacksCheckRecall

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {A B C D : CochainComplex V ℤ}
variable {a : A ⟶ B} {f g : B ⟶ C} {c : C ⟶ D}
variable (h : Homotopy f g) (i : ℤ)

/- Lemma 12.13.7 [0112]: a cochain homotopy can be whiskered simultaneously on its source and
target. -/
@[stacks 0112]
#check (Homotopy.whisker a h c : Homotopy ((a ≫ f) ≫ c) ((a ≫ g) ≫ c))

#check (Homotopy.whisker_hom a h c i (i - 1) :
  (Homotopy.whisker a h c).hom i (i - 1) =
    a.f i ≫ h.hom i (i - 1) ≫ c.f (i - 1))
