module

public import ReasLib.Algebra.Homology.Homotopy.Whisker
import StacksCheckRecall

@[expose] public section

open CategoryTheory HomologicalComplex

universe u v w

variable {ι : Type w} {V : Type u} [Category.{v} V] [Preadditive V]
variable {c : ComplexShape ι}
variable {A B C D : HomologicalComplex V c}
variable {f g : B ⟶ C}
variable (a : A ⟶ B) (h : Homotopy f g) (b : C ⟶ D)

/- Lemma 22.5.2 [09JP]: a homotopy remains a homotopy after precomposition and
postcomposition. The reusable owner is stated for homological complexes of arbitrary shape. -/
@[stacks 09JP]
#check (Homotopy.whisker a h b : Homotopy ((a ≫ f) ≫ b) ((a ≫ g) ≫ b))

/- The component of the whiskered homotopy is the corresponding triple composite. -/
#check @Homotopy.whisker_hom
