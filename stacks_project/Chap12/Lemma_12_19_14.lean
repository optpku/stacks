/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.Homology
import StacksCheckRecall

/-!
# Lemma 12.19.14

Source-facing check for the canonical identification of the associated graded of filtered
homology with the homology of the associated graded complex.  The concrete homology datum and
its fine-grained kernel/cokernel API are owned by ReasLib.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory.FilteredObject.Hom

open FilteredObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B D : FilteredObject C}

/- Lemma 12.19.14 [0128]: for a complex `A ⟶ B ⟶ D` of filtered objects with strict
differentials, `gr^p (ker β / im α)` is canonically the homology of the graded complex. -/
@[stacks 0128]
#check (Graded.ShortComplex.Homology.iso :
  (f : A ⟶ B) → (g : B ⟶ D) → (hfg : f ≫ g = 0) →
    Strict f → Strict g → (p : ℤ) →
      (FilteredObject.Subobject.Subquotient.object B
        (image_le_kernel f.hom g.hom (hom_comp_eq_zero f g hfg))).gradedPiece p ≅
        (Graded.ShortComplex.of f g hfg p).homology)

end CategoryTheory.FilteredObject.Hom
