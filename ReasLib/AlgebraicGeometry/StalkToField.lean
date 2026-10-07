module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.StructureSheaf

/-!
# Ringed-space morphisms from field-valued stalk homomorphisms

A homomorphism from the stalk of a scheme at a point to a field determines a
morphism of ringed spaces from the field's spectrum, with constant underlying map.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The constant continuous map from `Spec K` to a scheme with value `x`. -/
private def constSpecBase {X : Scheme.{u}} (x : X) (K : Type u) [Field K] :
    ((Spec (CommRingCat.of K)).toSheafedSpace : TopCat) ⟶ (X.toSheafedSpace : TopCat) :=
  TopCat.ofHom (ContinuousMap.const _ x)

/-- An open set containing `x` has full inverse image under the constant map to `x`. -/
private theorem constSpecBase_preimage_eq_top {X : Scheme.{u}} (x : X)
    {K : Type u} [Field K] {U : Opens X} (hx : x ∈ U) :
    (Opens.map (constSpecBase x K)).obj U = ⊤ := by
  ext p
  have hp : (constSpecBase x K) p = x := ContinuousMap.const_apply _ _
  simpa [hp] using hx

/-- An open set not containing `x` has empty inverse image under the constant map to `x`. -/
private theorem constSpecBase_preimage_eq_bot {X : Scheme.{u}} (x : X)
    {K : Type u} [Field K] {U : Opens X} (hx : x ∉ U) :
    (Opens.map (constSpecBase x K)).obj U = ⊥ := by
  ext p
  have hp : (constSpecBase x K) p = x := ContinuousMap.const_apply _ _
  simpa [hp] using hx

/-- A field-valued homomorphism from the stalk at `x` determines a morphism of
ringed spaces from the field's spectrum to the scheme. -/
def ringedSpaceHomOfStalkHom {X : Scheme.{u}} (x : X) {K : Type u} [Field K]
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of K) :
    (Spec (CommRingCat.of K)).toSheafedSpace ⟶ X.toSheafedSpace :=
  InducedCategory.homMk
    { base := constSpecBase x K
      c :=
        { app := fun U =>
            @dite _ (x ∈ unop U) (Classical.dec _)
              (fun hx =>
                X.presheaf.germ (unop U) x hx ≫ φ ≫
                  (StructureSheaf.globalSectionsIso K).hom ≫
                    (Spec (CommRingCat.of K)).presheaf.map
                      (eqToHom (constSpecBase_preimage_eq_top x hx)).op)
              (fun hx =>
                ((Spec (CommRingCat.of K)).sheaf.isTerminalOfEqEmpty
                    (constSpecBase_preimage_eq_bot x hx)).from
                  (X.presheaf.obj U))
          naturality := fun _ _ _ => sorry } }

/-- The morphism induced by a field-valued stalk homomorphism sends every point
of the field's spectrum to the chosen point. -/
theorem ringedSpaceHomOfStalkHom_apply {X : Scheme.{u}} (x : X) {K : Type u} [Field K]
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of K) (p : Spec (CommRingCat.of K)) :
    (ringedSpaceHomOfStalkHom x φ).hom p = x :=
  sorry

end AlgebraicGeometry.Scheme
