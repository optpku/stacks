module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_19_2_Adjunction

/-!
# Lemma 85.19.2

Let `C` be a site with fibre products and `X` an object of `C`. Let `K` be a
hypercovering of `X`. For every `E` in `D(C / X)`, the canonical derived-unit map
`E ⟶ Ra_* a⁻¹ E` is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SemiRepresentableFamily (overSiteDiagram overSiteTotalTopology totalForget)
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]
variable [h_pb : HasPullbacks C]
include h_pb
variable (J : GrothendieckTopology C) (X : C) (K : Hypercovering.{w} J X)
variable [HasSheafify (J.over X) AddCommGrpCat.{max w u v}]
variable [HasSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤
    AddCommGrpCat.{max w u v},
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.19.2: Let `C` be a site with fibre products and `X` an object of
`C`. Let `K` be a hypercovering of `X`. For `E ∈ D(C / X)` the map
`E ⟶ Ra_* a⁻¹ E` is an isomorphism. -/
@[stacks 0D8L]
theorem derivedUnit_app_isIso
    (E : DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max w u v})) :
    IsIso ((derivedUnit J X K).app E :
      E ⟶ (directImageDerived J X K).obj ((inverseImageDerived J X K).obj E)) :=
  sorry

/-- The derived unit `𝟭 ⟶ a⁻¹ ⋙ Ra_*` is an isomorphism of functors on `D(C / X)`. -/
theorem derivedUnit_isIso : IsIso (derivedUnit J X K) :=
  sorry

/-- Every `E ∈ D(C / X)` is isomorphic to `Ra_* a⁻¹ E`. -/
theorem isIsomorphic_inverseImageDirectImage
    (E : DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max w u v})) :
    IsIsomorphic E
      ((directImageDerived J X K).obj ((inverseImageDerived J X K).obj E)) :=
  sorry

end CategoryTheory.Hypercovering
