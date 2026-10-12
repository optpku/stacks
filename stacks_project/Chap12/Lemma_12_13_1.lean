/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.Homotopy.Whisker
import StacksCheckRecall

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {A B C D : ChainComplex V ℤ}
variable {a : A ⟶ B} {f g : B ⟶ C} {c : C ⟶ D}
variable (h : Homotopy f g) (i : ℤ)

/- Lemma 12.13.1 [010W]: a chain homotopy can be whiskered simultaneously on its source and
target. -/
@[stacks 010W]
#check (Homotopy.whisker a h c : Homotopy ((a ≫ f) ≫ c) ((a ≫ g) ≫ c))

#check (Homotopy.whisker_hom a h c i (i + 1) :
  (Homotopy.whisker a h c).hom i (i + 1) =
    a.f i ≫ h.hom i (i + 1) ≫ c.f (i + 1))
