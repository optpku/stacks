module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_17_3_Adjunction

/-!
# Lemma 85.17.3

Let `C` be a site with equalizers and fibre products, and let `K` be a
hypercovering. For every `E` in `D(C)`, the canonical derived-unit map
`E ⟶ Ra_* a⁻¹ E` is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [h_eq : HasEqualizers C] [h_pb : HasPullbacks C]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{w} J)
variable [HasSheafify J AddCommGrpCat.{max w u v}]
variable [HasSheafify (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.17.3: Let `C` be a site with equalizers and fibre products. Let `K` be a
hypercovering. For `E ∈ D(C)` the map `E ⟶ Ra_* a⁻¹ E` is an isomorphism. -/
@[stacks 0D8G]
theorem derivedUnit_app_isIso
    (E : DerivedCategory (Sheaf J AddCommGrpCat.{max w u v})) :
    IsIso ((derivedUnit J K).app E) :=
  sorry

/-- The derived unit `𝟭 ⟶ a⁻¹ ⋙ Ra_*` is an isomorphism of functors on `D(C)`. -/
theorem derivedUnit_isIso : IsIso (derivedUnit J K) :=
  sorry

/-- Every `E ∈ D(C)` is isomorphic to `Ra_* a⁻¹ E`. -/
theorem isIsomorphic_inverseImageDirectImage
    (E : DerivedCategory (Sheaf J AddCommGrpCat.{max w u v})) :
    IsIsomorphic E ((directImageDerived J K).obj ((inverseImageDerived J K).obj E)) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
