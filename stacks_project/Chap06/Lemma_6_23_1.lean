/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Algebraic.Morphisms
import StacksCheckRecall


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace

noncomputable section

universe w v u

section

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w) [F.Faithful]
variable {X Y : TopCat.{w}} (f : X ⟶ Y)
variable {ℱ : X.Sheaf C} {𝒢 : Y.Sheaf C}
variable [(Opens.grothendieckTopology Y).HasSheafCompose F]

/- The source concerns ordinary algebraic categories through their faithful underlying-set functor.
Using an arbitrary faithful `F : C ⥤ Type w` is the exact reusable boundary: `Sheaf.pushforward C f`
and `sheafCompose JY F` are the canonical owners, while the sectionwise lifting hypothesis retains
the textbook presentation and specializes to `F = CategoryTheory.forget C`. -/
/- Lemma 6.23.1: an `f`-map of the underlying sheaves of sets of `C`-valued sheaves comes from a
unique `f`-morphism of sheaves of algebraic structures if each section map is induced by a
morphism in `C`. -/
@[stacks 008Q]
#check TopCat.Sheaf.Algebraic.existsUnique_pushforwardHom_of_sectionwise F f

end
