module

public import ReasLib.CategoryTheory.Adjunction.IsomorphismProperty
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom equivalences on the counit-isomorphism locus

An adjunction identifies maps out of `F.obj (G.obj K)` with maps out of `G.obj K`.  When the
counit at `K` is invertible, this gives a canonical equivalence with maps out of `K` itself.
The owner is phrased with the adjunction as the primary datum so that the two functors are inferred
instead of being repeated in every downstream statement.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe vC vD uC uD

namespace CategoryTheory.Adjunction

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- Maps out of a counit-isomorphism object are transported through the adjunction. -/
@[stacks 0H0S "hom equivalence on the counit-isomorphism locus"]
noncomputable abbrev homEquiv_of_counitIso
    (K : D) (hK : adj.counitIsoProperty K) (M : D) :
    (K ⟶ M) ≃ (G.obj K ⟶ G.obj M) :=
  let _ : IsIso (adj.counit.app K) := hK
  (Iso.homCongr (asIso (adj.counit.app K)).symm (Iso.refl M)).trans
    (adj.homEquiv (G.obj K) M)

/-- Forward computation for `homEquiv_of_counitIso`. -/
@[stacks 0H0S "forward counit hom equivalence computation"]
theorem homEquiv_of_counitIso_apply
    (K : D) (hK : adj.counitIsoProperty K) (M : D) (f : K ⟶ M) :
    adj.homEquiv_of_counitIso K hK M f =
      adj.homEquiv (G.obj K) M (adj.counit.app K ≫ f) := sorry

/-- Inverse computation for `homEquiv_of_counitIso`. -/
@[stacks 0H0S "inverse counit hom equivalence computation"]
theorem homEquiv_of_counitIso_symm_apply
    (K : D) (hK : adj.counitIsoProperty K) (M : D) (g : G.obj K ⟶ G.obj M) :
    (adj.homEquiv_of_counitIso K hK M).symm g =
      (asIso (adj.counit.app K)).inv ≫ (adj.homEquiv (G.obj K) M).symm g := sorry

/-- The counit hom equivalence restricted to an object-property full subcategory. -/
@[stacks 0H0S "hom equivalence on a counit-isomorphism subcategory"]
noncomputable abbrev homEquiv_of_counitIsoOn
    (P : ObjectProperty D) (hP : P ≤ adj.counitIsoProperty)
    (K : P.FullSubcategory) (M : D) :
    (K.obj ⟶ M) ≃ (G.obj K.obj ⟶ G.obj M) :=
  adj.homEquiv_of_counitIso K.obj (hP K.obj K.property) M

/-- Forward computation for the full-subcategory counit hom equivalence. -/
@[stacks 0H0S "forward subcategory counit hom equivalence computation"]
theorem homEquiv_of_counitIsoOn_apply
    (P : ObjectProperty D) (hP : P ≤ adj.counitIsoProperty)
    (K : P.FullSubcategory) (M : D) (f : K.obj ⟶ M) :
    adj.homEquiv_of_counitIsoOn P hP K M f =
      adj.homEquiv (G.obj K.obj) M (adj.counit.app K.obj ≫ f) := sorry

end CategoryTheory.Adjunction

end
