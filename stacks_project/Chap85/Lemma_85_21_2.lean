module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import stacks_project.Chap85.Lemma_85_19_2

/-!
# Lemma 85.21.2

Let `C` be a site with fibre products and `X` an object of `C`. Let
`a : U ⟶ X` be a hypercovering of `X` in `C`. For every `E` in `D(C / X)`,
the canonical derived-unit map `E ⟶ Ra_* a⁻¹ E` is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SemiRepresentableFamily (overSiteDiagram overSiteTotalTopology totalForget)
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]
variable [h_pb : HasPullbacks C]
include h_pb
variable (J : GrothendieckTopology C) (A : SimplicialObject.Augmented C)
variable (hA : A.IsHypercovering J)
variable [HasSheafify (J.over A.right) AddCommGrpCat.{max w u v}]
variable [HasSheafify
    (overSiteTotalTopology (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck
      (overSiteDiagram (toHypercovering.{w} A hA).toSimplicialObject))ᵒᵖ ⥤
    AddCommGrpCat.{max w u v},
    (totalForget (toHypercovering.{w} A hA).toSimplicialObject).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.21.2: Let `C` be a site with fibre products and `X` an object of
`C`. Let `a : U ⟶ X` be a hypercovering of `X` in `C` as defined above. For
`E ∈ D(C / X)` the map `E ⟶ Ra_* a⁻¹ E` is an isomorphism. -/
@[stacks 0D8N]
theorem derivedUnit_app_isIso
    (E : DerivedCategory (Sheaf (J.over A.right) AddCommGrpCat.{max w u v})) :
    IsIso ((Hypercovering.derivedUnit J A.right (toHypercovering.{w} A hA)).app E :
      E ⟶ (Hypercovering.directImageDerived J A.right (toHypercovering.{w} A hA)).obj
        ((Hypercovering.inverseImageDerived J A.right (toHypercovering.{w} A hA)).obj E)) :=
  sorry

/-- The derived unit `𝟭 ⟶ a⁻¹ ⋙ Ra_*` is an isomorphism of functors on `D(C / X)`. -/
theorem derivedUnit_isIso :
    IsIso (Hypercovering.derivedUnit J A.right (toHypercovering.{w} A hA)) :=
  sorry

/-- Every `E ∈ D(C / X)` is isomorphic to `Ra_* a⁻¹ E`. -/
theorem isIsomorphic_inverseImageDirectImage
    (E : DerivedCategory (Sheaf (J.over A.right) AddCommGrpCat.{max w u v})) :
    IsIsomorphic E
      ((Hypercovering.directImageDerived J A.right (toHypercovering.{w} A hA)).obj
        ((Hypercovering.inverseImageDerived J A.right (toHypercovering.{w} A hA)).obj E)) :=
  sorry

end CategoryTheory.SimplicialObject.Augmented
