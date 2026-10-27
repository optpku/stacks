/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.DerivedAdjunction

/-!
# Derived adjunction of a hypercovering of an object

The slice derived-adjunction interface is provided by its shared mathematical
owner. These checks record its exact functor, adjunction, and unit types.
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

#check (inverseImageExact J X K :
    Sheaf (J.over X) AddCommGrpCat.{max w u v} ⥤ₑ
      Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
        AddCommGrpCat.{max w u v})

#check (inverseImageDerived J X K :
    DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory
        (Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
          AddCommGrpCat.{max w u v}))

#check (directImageDerived J X K :
    DerivedCategory
        (Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
          AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max w u v}))

#check (derivedAdjunction J X K :
    inverseImageDerived J X K ⊣ directImageDerived J X K)

#check (derivedUnit J X K :
    𝟭 (DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max w u v})) ⟶
      inverseImageDerived J X K ⋙ directImageDerived J X K)

end CategoryTheory.Hypercovering
