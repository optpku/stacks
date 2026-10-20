module

public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Contraction

/-!
# Evaluating contracted adjunction resolutions

This leaf evaluates both functor-level contractions at objects. It retains the concrete
pointwise extra degeneracies, inverses, homotopies, and bundled homotopy equivalences rather
than exposing only the final property. The uncontracted evaluation functors live in
`Construction`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject
open Opposite
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe uA uS vA vS

namespace CategoryTheory.Adjunction.SimplicialResolution

variable {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
variable {U : S ⥤ A} {V : A ⥤ S}

/-- The last extra degeneracy on the postcomposed adjunction resolution evaluated at an object. -/
@[stacks 08ND "pointwise last extra degeneracy for an adjunction resolution"]
noncomputable def postcompose.eval.lastExtraDegeneracy (adj : U ⊣ V) (X : A) :
    SimplicialObject.Augmented.LastExtraDegeneracy
      ((postcompose.eval adj).obj X) :=
  (postcompose.lastExtraDegeneracy adj).app X

/-- The pointwise postcomposed zero-section is the adjunction unit at the image of the resolved
object under the right adjoint. -/
@[simp, stacks 08ND "pointwise postcomposed zero-section"]
theorem postcompose.eval.lastExtraDegeneracy.s' (adj : U ⊣ V) (X : A) :
    (postcompose.eval.lastExtraDegeneracy adj X).s' =
      adj.unit.app (V.obj X) := sorry

/-- The maps of the pointwise last extra degeneracy are the evaluated unit insertions. -/
@[simp, stacks 08ND "pointwise postcomposed last-degeneracy maps"]
theorem postcompose.eval.lastExtraDegeneracy.s
    (adj : U ⊣ V) (X : A) (n : ℕ) :
    (postcompose.eval.lastExtraDegeneracy adj X).s n =
      (postcompose.lastDegeneracy adj n).app X := sorry

/-- The extra degeneracy on the precomposed adjunction resolution evaluated at an object. -/
@[stacks 08ND "pointwise extra degeneracy for an adjunction resolution"]
noncomputable def precompose.eval.extraDegeneracy (adj : U ⊣ V) (X : S) :
    SimplicialObject.Augmented.ExtraDegeneracy
      ((precompose.eval adj).obj X) :=
  (precompose.extraDegeneracy adj).app X

/-- The pointwise precomposed zero-section is the left-adjoint image of the adjunction unit. -/
@[simp, stacks 08ND "pointwise precomposed zero-section"]
theorem precompose.eval.extraDegeneracy.s' (adj : U ⊣ V) (X : S) :
    (precompose.eval.extraDegeneracy adj X).s' =
      U.map (adj.unit.app X) := sorry

/-- The maps of the pointwise extra degeneracy are the evaluated unit insertions. -/
@[simp, stacks 08ND "pointwise precomposed extra-degeneracy maps"]
theorem precompose.eval.extraDegeneracy.s
    (adj : U ⊣ V) (X : S) (n : ℕ) :
    (precompose.eval.extraDegeneracy adj X).s n =
      (precompose.extraDegeneracyMap adj n).app X := sorry

/-- The canonical inverse of the pointwise postcomposed augmentation. -/
@[stacks 08ND "pointwise postcomposed adjunction-resolution inverse"]
noncomputable def postcompose.eval.inverse (adj : U ⊣ V) (X : A) :
    (const S).obj ((postcompose.eval adj).obj X).right ⟶
      ((postcompose.eval adj).obj X).left :=
  (postcompose.eval.lastExtraDegeneracy adj X).section_

/-- The pointwise postcomposed inverse is the objectwise value of the functor-level inverse. -/
@[simp, stacks 08ND "pointwise postcomposed inverse component"]
theorem postcompose.eval.inverse.app (adj : U ⊣ V) (X : A)
    (Δ : SimplexCategoryᵒᵖ) :
    (postcompose.eval.inverse adj X).app Δ =
      ((postcompose.inverse adj).app Δ).app X := sorry

/-- In degree zero, the pointwise postcomposed inverse is the adjunction unit. -/
@[simp, stacks 08ND "pointwise postcomposed inverse in degree zero"]
theorem postcompose.eval.inverse.app_zero (adj : U ⊣ V) (X : A) :
    (postcompose.eval.inverse adj X).app (op ⦋0⦌) =
      adj.unit.app (V.obj X) := sorry

/-- The pointwise postcomposed inverse is a strict section of the augmentation. -/
@[simp, stacks 08ND "pointwise postcomposed inverse section"]
theorem postcompose.eval.inverse.comp_hom (adj : U ⊣ V) (X : A) :
    postcompose.eval.inverse adj X ≫ ((postcompose.eval adj).obj X).hom =
      𝟙 ((const S).obj ((postcompose.eval adj).obj X).right) := sorry

/-- The canonical inverse of the pointwise precomposed augmentation. -/
@[stacks 08ND "pointwise precomposed adjunction-resolution inverse"]
noncomputable def precompose.eval.inverse (adj : U ⊣ V) (X : S) :
    (const A).obj ((precompose.eval adj).obj X).right ⟶
      ((precompose.eval adj).obj X).left :=
  (precompose.eval.extraDegeneracy adj X).section_

/-- The pointwise precomposed inverse is the objectwise value of the functor-level inverse. -/
@[simp, stacks 08ND "pointwise precomposed inverse component"]
theorem precompose.eval.inverse.app (adj : U ⊣ V) (X : S)
    (Δ : SimplexCategoryᵒᵖ) :
    (precompose.eval.inverse adj X).app Δ =
      ((precompose.inverse adj).app Δ).app X := sorry

/-- In degree zero, the pointwise precomposed inverse is the left-adjoint image of the unit. -/
@[simp, stacks 08ND "pointwise precomposed inverse in degree zero"]
theorem precompose.eval.inverse.app_zero (adj : U ⊣ V) (X : S) :
    (precompose.eval.inverse adj X).app (op ⦋0⦌) =
      U.map (adj.unit.app X) := sorry

/-- The pointwise precomposed inverse is a strict section of the augmentation. -/
@[simp, stacks 08ND "pointwise precomposed inverse section"]
theorem precompose.eval.inverse.comp_hom (adj : U ⊣ V) (X : S) :
    precompose.eval.inverse adj X ≫ ((precompose.eval adj).obj X).hom =
      𝟙 ((const A).obj ((precompose.eval adj).obj X).right) := sorry

/-- The concrete contraction of the pointwise postcomposed adjunction resolution. -/
@[stacks 08ND "pointwise postcomposed adjunction-resolution contraction"]
noncomputable def postcompose.eval.homotopy (adj : U ⊣ V) (X : A) :
    Homotopy (𝟙 ((postcompose.eval adj).obj X).left)
      (((postcompose.eval adj).obj X).hom ≫ postcompose.eval.inverse adj X) :=
  (postcompose.eval.lastExtraDegeneracy adj X).homotopy

/-- The concrete contraction of the pointwise precomposed adjunction resolution. -/
@[stacks 08ND "pointwise precomposed adjunction-resolution contraction"]
noncomputable def precompose.eval.homotopy (adj : U ⊣ V) (X : S) :
    Homotopy
      (((precompose.eval adj).obj X).hom ≫ precompose.eval.inverse adj X)
      (𝟙 ((precompose.eval adj).obj X).left) :=
  (precompose.eval.extraDegeneracy adj X).homotopy

/-- The pointwise postcomposed resolution with its canonical unit-induced homotopy inverse. -/
@[stacks 08ND "pointwise postcomposed adjunction-resolution equivalence"]
noncomputable def postcompose.eval.homotopyEquiv (adj : U ⊣ V) (X : A) :
    HomotopyEquiv ((postcompose.eval adj).obj X).left
      ((const S).obj ((postcompose.eval adj).obj X).right) :=
  (postcompose.eval.lastExtraDegeneracy adj X).simplicialHomotopyEquiv

/-- The pointwise precomposed resolution with its canonical unit-induced homotopy inverse. -/
@[stacks 08ND "pointwise precomposed adjunction-resolution equivalence"]
noncomputable def precompose.eval.homotopyEquiv (adj : U ⊣ V) (X : S) :
    HomotopyEquiv ((precompose.eval adj).obj X).left
      ((const A).obj ((precompose.eval adj).obj X).right) :=
  (precompose.eval.extraDegeneracy adj X).simplicialHomotopyEquiv

/-- The forward map of the pointwise postcomposed equivalence is its augmentation. -/
@[simp, stacks 08ND "pointwise postcomposed equivalence forward map"]
theorem postcompose.eval.homotopyEquiv.hom (adj : U ⊣ V) (X : A) :
    (postcompose.eval.homotopyEquiv adj X).hom =
      ((postcompose.eval adj).obj X).hom := sorry

/-- The inverse map of the pointwise postcomposed equivalence is its canonical section. -/
@[simp, stacks 08ND "pointwise postcomposed equivalence inverse map"]
theorem postcompose.eval.homotopyEquiv.inv (adj : U ⊣ V) (X : A) :
    (postcompose.eval.homotopyEquiv adj X).inv =
      postcompose.eval.inverse adj X := sorry

/-- The forward map of the pointwise precomposed equivalence is its augmentation. -/
@[simp, stacks 08ND "pointwise precomposed equivalence forward map"]
theorem precompose.eval.homotopyEquiv.hom (adj : U ⊣ V) (X : S) :
    (precompose.eval.homotopyEquiv adj X).hom =
      ((precompose.eval adj).obj X).hom := sorry

/-- The inverse map of the pointwise precomposed equivalence is its canonical section. -/
@[simp, stacks 08ND "pointwise precomposed equivalence inverse map"]
theorem precompose.eval.homotopyEquiv.inv (adj : U ⊣ V) (X : S) :
    (precompose.eval.homotopyEquiv adj X).inv =
      precompose.eval.inverse adj X := sorry

/-- Every pointwise postcomposed augmentation is a simplicial homotopy equivalence. -/
@[stacks 08ND "pointwise postcomposed augmentation is a homotopy equivalence"]
theorem postcompose.eval.isHomotopyEquivalence (adj : U ⊣ V) (X : A) :
    IsHomotopyEquivalence ((postcompose.eval adj).obj X).hom := sorry

/-- Every pointwise precomposed augmentation is a simplicial homotopy equivalence. -/
@[stacks 08ND "pointwise precomposed augmentation is a homotopy equivalence"]
theorem precompose.eval.isHomotopyEquivalence (adj : U ⊣ V) (X : S) :
    IsHomotopyEquivalence ((precompose.eval adj).obj X).hom := sorry

end CategoryTheory.Adjunction.SimplicialResolution
