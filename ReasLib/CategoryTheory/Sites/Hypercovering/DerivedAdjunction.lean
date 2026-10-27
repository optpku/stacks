/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Slice
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.DerivedAdjunction

/-!
# Derived adjunctions for hypercoverings of an object

The terminal hypercovering on the slice site induces exact inverse image,
unbounded derived inverse and direct images, their adjunction, and its unit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SemiRepresentableFamily
  (overSiteDiagram overSiteTotalTopology totalForget)
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

/-- The exact inverse-image functor `a⁻¹` on abelian sheaves along `j_total` for a
hypercovering of an object. -/
abbrev inverseImageExact :
    Sheaf (J.over X) AddCommGrpCat.{max w u v} ⥤ₑ
      Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
        AddCommGrpCat.{max w u v} :=
  SemiRepresentableFamily.inverseImageExact.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- Unbounded derived inverse image `a⁻¹` on `D(C / X)`. -/
abbrev inverseImageDerived :
    DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory
        (Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
          AddCommGrpCat.{max w u v}) :=
  SemiRepresentableFamily.inverseImageDerived.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- Unbounded total right-derived direct image `Ra_*` along `j_total` for a
hypercovering of an object. -/
abbrev directImageDerived :
    DerivedCategory
        (Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
          AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max w u v}) :=
  SemiRepresentableFamily.directImageDerived.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- The unbounded derived adjunction `a⁻¹ ⊣ Ra_*` attached to a hypercovering of an
object. -/
def derivedAdjunction :
    inverseImageDerived J X K ⊣ directImageDerived J X K :=
  SemiRepresentableFamily.derivedAdjunction.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- The canonical derived unit `E ⟶ Ra_* a⁻¹ E` on `D(C / X)`. -/
abbrev derivedUnit :
    𝟭 (DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max w u v})) ⟶
      inverseImageDerived J X K ⋙ directImageDerived J X K :=
  SemiRepresentableFamily.derivedUnit.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

end CategoryTheory.Hypercovering
