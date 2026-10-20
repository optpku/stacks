module

public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit owners for derived internal Hom

This leaf owns the internal-Hom object selected by an explicit closed structure and the canonical
comparison between two such choices.  The canonical enriched `RHom` facade lives in the sibling
`InternalHom.Model.RHom` leaf; its compatibility with a selected closed owner is recorded only in
the optional `InternalHom.Model.RHom.Closed` leaf, rather than inferred from a closed structure
alone.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe w v u

open CategoryTheory

namespace CategoryTheory.DerivedCategory.InternalHom

variable {A : Type u} [CommRing A]
variable [HasDerivedCategory.{w} (ModuleCat.{v} A)]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{v} A))]

/-- Stacks `0E1U`: the internal-Hom object selected by an explicit closed owner. -/
@[stacks 0E1U "selected derived internal-Hom object"]
noncomputable abbrev obj
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{v} A)))
    (L M : DerivedCategory (ModuleCat.{v} A)) : DerivedCategory (ModuleCat.{v} A) :=
  (MonoidalClosed.ihomOf H L).obj M

/-- The natural isomorphism between the fixed-source internal-Hom functors selected by two
explicit closed owners.  This is the reusable uniqueness owner; objectwise comparisons are its
components. -/
@[stacks 0E1U "change of derived internal-Hom functor owner"]
noncomputable def choiceFunctorIso
    (H H' : MonoidalClosed (DerivedCategory (ModuleCat.{v} A)))
    (L : DerivedCategory (ModuleCat.{v} A)) :
    MonoidalClosed.ihomOf H L ≅ MonoidalClosed.ihomOf H' L :=
  (MonoidalClosed.adjunctionOf H L).rightAdjointUniq
    (MonoidalClosed.adjunctionOf H' L)

namespace choiceFunctorIso

/-- Changing a selected internal-Hom functor owner to itself gives the identity isomorphism. -/
@[simp, stacks 0E1U "identity comparison for a derived internal-Hom functor owner"]
theorem refl
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{v} A)))
    (L : DerivedCategory (ModuleCat.{v} A)) :
    choiceFunctorIso H H L = Iso.refl (MonoidalClosed.ihomOf H L) := by
  apply Iso.ext
  exact Adjunction.rightAdjointUniq_refl (MonoidalClosed.adjunctionOf H L)

/-- Reversing a selected internal-Hom functor comparison exchanges its two owners. -/
@[stacks 0E1U "symmetric comparison for a derived internal-Hom functor owner"]
theorem symm
    (H H' : MonoidalClosed (DerivedCategory (ModuleCat.{v} A)))
    (L : DerivedCategory (ModuleCat.{v} A)) :
    (choiceFunctorIso H H' L).symm = choiceFunctorIso H' H L := by
  apply Iso.ext
  ext M
  exact Adjunction.rightAdjointUniq_inv_app
    (MonoidalClosed.adjunctionOf H L) (MonoidalClosed.adjunctionOf H' L) M

/-- Comparisons between three selected internal-Hom functor owners compose transitively. -/
@[simp, stacks 0E1U "transitive comparison for derived internal-Hom functor owners"]
theorem trans
    (H₀ H₁ H₂ : MonoidalClosed (DerivedCategory (ModuleCat.{v} A)))
    (L : DerivedCategory (ModuleCat.{v} A)) :
    choiceFunctorIso H₀ H₁ L ≪≫ choiceFunctorIso H₁ H₂ L =
      choiceFunctorIso H₀ H₂ L := by
  apply Iso.ext
  exact Adjunction.rightAdjointUniq_trans
    (MonoidalClosed.adjunctionOf H₀ L) (MonoidalClosed.adjunctionOf H₁ L)
      (MonoidalClosed.adjunctionOf H₂ L)

end choiceFunctorIso

/-- The canonical comparison between internal-Hom objects selected by two closed owners. -/
@[stacks 0E1U "change of derived internal-Hom owner"]
noncomputable def choiceIso
    (H H' : MonoidalClosed (DerivedCategory (ModuleCat.{v} A)))
    (L M : DerivedCategory (ModuleCat.{v} A)) :
    obj H L M ≅ obj H' L M :=
  (choiceFunctorIso H H' L).app M

namespace choiceIso

/-- The forward map of the comparison between two selected derived internal-Hom owners. -/
@[simp, stacks 0E1U "forward map of a derived internal-Hom owner comparison"]
theorem hom
    (H H' : MonoidalClosed (DerivedCategory (ModuleCat.{v} A)))
    (L M : DerivedCategory (ModuleCat.{v} A)) :
    (choiceIso H H' L M).hom =
      ((MonoidalClosed.adjunctionOf H L).rightAdjointUniq
        (MonoidalClosed.adjunctionOf H' L)).hom.app M := rfl

/-- The inverse map of the comparison between two selected derived internal-Hom owners. -/
@[simp, stacks 0E1U "inverse map of a derived internal-Hom owner comparison"]
theorem inv
    (H H' : MonoidalClosed (DerivedCategory (ModuleCat.{v} A)))
    (L M : DerivedCategory (ModuleCat.{v} A)) :
    (choiceIso H H' L M).inv =
      ((MonoidalClosed.adjunctionOf H L).rightAdjointUniq
        (MonoidalClosed.adjunctionOf H' L)).inv.app M := rfl

/-- Changing the closed owner commutes with maps in the target variable. -/
@[reassoc, stacks 0E1U "naturality of a derived internal-Hom owner comparison"]
theorem naturality
    (H H' : MonoidalClosed (DerivedCategory (ModuleCat.{v} A)))
    (L : DerivedCategory (ModuleCat.{v} A)) {M M' : DerivedCategory (ModuleCat.{v} A)}
    (f : M ⟶ M') :
    (MonoidalClosed.ihomOf H L).map f ≫ (choiceIso H H' L M').hom =
      (choiceIso H H' L M).hom ≫ (MonoidalClosed.ihomOf H' L).map f :=
  (choiceFunctorIso H H' L).hom.naturality f

/-- The inverse owner comparison is natural in the target variable as well. -/
@[reassoc, stacks 0E1U "naturality of the inverse internal-Hom owner comparison"]
theorem inv_naturality
    (H H' : MonoidalClosed (DerivedCategory (ModuleCat.{v} A)))
    (L : DerivedCategory (ModuleCat.{v} A)) {M M' : DerivedCategory (ModuleCat.{v} A)}
    (f : M ⟶ M') :
    (MonoidalClosed.ihomOf H' L).map f ≫ (choiceIso H H' L M').inv =
      (choiceIso H H' L M).inv ≫ (MonoidalClosed.ihomOf H L).map f :=
  (choiceFunctorIso H H' L).inv.naturality f

/-- Changing a derived internal-Hom owner to itself gives the identity comparison. -/
@[simp, stacks 0E1U "identity comparison for a derived internal-Hom owner"]
theorem refl
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{v} A)))
    (L M : DerivedCategory (ModuleCat.{v} A)) :
    choiceIso H H L M = Iso.refl (obj H L M) := by
  apply Iso.ext
  change (choiceFunctorIso H H L).hom.app M = (Iso.refl _).hom
  rw [choiceFunctorIso.refl]
  rfl

/-- Reversing a derived internal-Hom owner comparison swaps its two owners. -/
@[stacks 0E1U "symmetric comparison for a derived internal-Hom owner"]
theorem symm
    (H H' : MonoidalClosed (DerivedCategory (ModuleCat.{v} A)))
    (L M : DerivedCategory (ModuleCat.{v} A)) :
    (choiceIso H H' L M).symm = choiceIso H' H L M := by
  apply Iso.ext
  change ((choiceFunctorIso H H' L).symm).hom.app M =
    (choiceFunctorIso H' H L).hom.app M
  rw [choiceFunctorIso.symm]

/-- Comparisons between three derived internal-Hom owners compose transitively. -/
@[simp, stacks 0E1U "transitive comparison for derived internal-Hom owners"]
theorem trans
    (H₀ H₁ H₂ : MonoidalClosed (DerivedCategory (ModuleCat.{v} A)))
    (L M : DerivedCategory (ModuleCat.{v} A)) :
    choiceIso H₀ H₁ L M ≪≫ choiceIso H₁ H₂ L M = choiceIso H₀ H₂ L M := by
  apply Iso.ext
  change (choiceFunctorIso H₀ H₁ L ≪≫ choiceFunctorIso H₁ H₂ L).hom.app M =
    (choiceFunctorIso H₀ H₂ L).hom.app M
  rw [choiceFunctorIso.trans]

end choiceIso

/- The notation is owned here so downstream chapters do not need a chapter-specific closed owner
or a temporary typeclass pin. -/
set_option quotPrecheck false in
scoped[DerivedInternalHom] notation:70 "RHom[" H:70 "](" L:70 ", " M:70 ")" =>
  CategoryTheory.DerivedCategory.InternalHom.obj H L M

end CategoryTheory.DerivedCategory.InternalHom
