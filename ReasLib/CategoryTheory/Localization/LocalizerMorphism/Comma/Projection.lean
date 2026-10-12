/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Comma.Computation

/-!
# Projection comparisons for localizer-morphism comma functors

The induced localization-comma functors commute with their source/target projections by
canonical natural isomorphisms whose components are identities.  Whiskering these comparisons
gives the diagram isomorphisms needed by pointwise Kan-extension and derived-functor arguments,
without transporting diagrams through an equality of functors.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.LocalizerMorphism

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace costructuredArrow

/-- Naturality of the identity components comparing the two source projections from the
induced localization costructured-arrow functor. -/
theorem compProjComponent_naturality (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    {U V : CostructuredArrow W₁.Q (W₁.Q.obj X)} (f : U ⟶ V) :
    (Φ.costructuredArrow X ⋙
          CostructuredArrow.proj W₂.Q (W₂.Q.obj (Φ.functor.obj X))).map f ≫
        𝟙 (Φ.functor.obj V.left) =
      𝟙 (Φ.functor.obj U.left) ≫
        (CostructuredArrow.proj W₁.Q (W₁.Q.obj X) ⋙ Φ.functor).map f := sorry

/-- The induced localization costructured-arrow functor commutes with the source projection by
an identity-component natural isomorphism. -/
@[stacks 05T5 "source-projection comparison for a localizer-morphism comma functor"]
noncomputable def compProjIso (Φ : LocalizerMorphism W₁ W₂) (X : C₁) :
    Φ.costructuredArrow X ⋙
        CostructuredArrow.proj W₂.Q (W₂.Q.obj (Φ.functor.obj X)) ≅
      CostructuredArrow.proj W₁.Q (W₁.Q.obj X) ⋙ Φ.functor :=
  NatIso.ofComponents (fun U => Iso.refl (Φ.functor.obj U.left))
    (compProjComponent_naturality Φ X)

namespace compProjIso

/-- The forward source-projection comparison component is the identity. -/
@[simp]
theorem hom_app (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : CostructuredArrow W₁.Q (W₁.Q.obj X)) :
    (compProjIso Φ X).hom.app U = 𝟙 (Φ.functor.obj U.left) := sorry

/-- The inverse source-projection comparison component is the identity. -/
@[simp]
theorem inv_app (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : CostructuredArrow W₁.Q (W₁.Q.obj X)) :
    (compProjIso Φ X).inv.app U = 𝟙 (Φ.functor.obj U.left) := sorry

end compProjIso

/-- Whiskering the source-projection comparison by a target functor gives the canonical
comparison between the corresponding costructured-arrow diagrams. -/
@[stacks 05T5 "diagram comparison for a localizer-morphism costructured-arrow functor"]
noncomputable def diagramIso (Φ : LocalizerMorphism W₁ W₂) (X : C₁) (F : C₂ ⥤ D) :
    (Φ.costructuredArrow X ⋙
        CostructuredArrow.proj W₂.Q (W₂.Q.obj (Φ.functor.obj X))) ⋙ F ≅
      (CostructuredArrow.proj W₁.Q (W₁.Q.obj X) ⋙ Φ.functor) ⋙ F :=
  Functor.isoWhiskerRight (compProjIso Φ X) F

namespace diagramIso

/-- The forward costructured-arrow diagram comparison has identity components. -/
@[simp]
theorem hom_app (Φ : LocalizerMorphism W₁ W₂) (X : C₁) (F : C₂ ⥤ D)
    (U : CostructuredArrow W₁.Q (W₁.Q.obj X)) :
    (diagramIso Φ X F).hom.app U = 𝟙 (F.obj (Φ.functor.obj U.left)) := sorry

/-- The inverse costructured-arrow diagram comparison has identity components. -/
@[simp]
theorem inv_app (Φ : LocalizerMorphism W₁ W₂) (X : C₁) (F : C₂ ⥤ D)
    (U : CostructuredArrow W₁.Q (W₁.Q.obj X)) :
    (diagramIso Φ X F).inv.app U = 𝟙 (F.obj (Φ.functor.obj U.left)) := sorry

end diagramIso

/-- Transport the costructured-arrow projection comparison across an arbitrary functor-level
comparison `Φ.functor ⋙ F₂ ≅ F₁ ⋙ G`.  Applications provide only that comparison; all
reassociation and whiskering is owned here. -/
@[stacks 05T5 "functor-level diagram comparison for a costructured-arrow functor"]
noncomputable def diagramIsoOfIso (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    {D₁ : Type u₃} {D₂ : Type u₄} [Category.{v₃} D₁] [Category.{v₄} D₂]
    {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} {G : D₁ ⥤ D₂}
    (e : Φ.functor ⋙ F₂ ≅ F₁ ⋙ G) :
    Φ.costructuredArrow X ⋙
        (CostructuredArrow.proj W₂.Q (W₂.Q.obj (Φ.functor.obj X)) ⋙ F₂) ≅
      (CostructuredArrow.proj W₁.Q (W₁.Q.obj X) ⋙ F₁) ⋙ G :=
  (Functor.associator (Φ.costructuredArrow X)
      (CostructuredArrow.proj W₂.Q (W₂.Q.obj (Φ.functor.obj X))) F₂).symm ≪≫
    diagramIso Φ X F₂ ≪≫
    Functor.associator (CostructuredArrow.proj W₁.Q (W₁.Q.obj X)) Φ.functor F₂ ≪≫
    Functor.isoWhiskerLeft (CostructuredArrow.proj W₁.Q (W₁.Q.obj X)) e ≪≫
    (Functor.associator (CostructuredArrow.proj W₁.Q (W₁.Q.obj X)) F₁ G).symm

namespace diagramIsoOfIso

/-- The forward functor-level costructured-arrow comparison is computed pointwise by `e.hom`. -/
@[simp]
theorem hom_app (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    {D₁ : Type u₃} {D₂ : Type u₄} [Category.{v₃} D₁] [Category.{v₄} D₂]
    {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} {G : D₁ ⥤ D₂}
    (e : Φ.functor ⋙ F₂ ≅ F₁ ⋙ G)
    (U : CostructuredArrow W₁.Q (W₁.Q.obj X)) :
    (diagramIsoOfIso Φ X e).hom.app U = e.hom.app U.left := sorry

/-- The inverse functor-level costructured-arrow comparison is computed pointwise by `e.inv`. -/
@[simp]
theorem inv_app (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    {D₁ : Type u₃} {D₂ : Type u₄} [Category.{v₃} D₁] [Category.{v₄} D₂]
    {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} {G : D₁ ⥤ D₂}
    (e : Φ.functor ⋙ F₂ ≅ F₁ ⋙ G)
    (U : CostructuredArrow W₁.Q (W₁.Q.obj X)) :
    (diagramIsoOfIso Φ X e).inv.app U = e.inv.app U.left := sorry

end diagramIsoOfIso

end costructuredArrow

namespace structuredArrow

/-- Naturality of the identity components comparing the two target projections from the
induced localization structured-arrow functor. -/
theorem compProjComponent_naturality (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    {U V : StructuredArrow (W₁.Q.obj X) W₁.Q} (f : U ⟶ V) :
    (Φ.structuredArrow X ⋙
          StructuredArrow.proj (W₂.Q.obj (Φ.functor.obj X)) W₂.Q).map f ≫
        𝟙 (Φ.functor.obj V.right) =
      𝟙 (Φ.functor.obj U.right) ≫
        (StructuredArrow.proj (W₁.Q.obj X) W₁.Q ⋙ Φ.functor).map f := sorry

/-- The induced localization structured-arrow functor commutes with the target projection by an
identity-component natural isomorphism. -/
@[stacks 05T5 "target-projection comparison for a localizer-morphism comma functor"]
noncomputable def compProjIso (Φ : LocalizerMorphism W₁ W₂) (X : C₁) :
    Φ.structuredArrow X ⋙
        StructuredArrow.proj (W₂.Q.obj (Φ.functor.obj X)) W₂.Q ≅
      StructuredArrow.proj (W₁.Q.obj X) W₁.Q ⋙ Φ.functor :=
  NatIso.ofComponents (fun U => Iso.refl (Φ.functor.obj U.right))
    (compProjComponent_naturality Φ X)

namespace compProjIso

/-- The forward target-projection comparison component is the identity. -/
@[simp]
theorem hom_app (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : StructuredArrow (W₁.Q.obj X) W₁.Q) :
    (compProjIso Φ X).hom.app U = 𝟙 (Φ.functor.obj U.right) := sorry

/-- The inverse target-projection comparison component is the identity. -/
@[simp]
theorem inv_app (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : StructuredArrow (W₁.Q.obj X) W₁.Q) :
    (compProjIso Φ X).inv.app U = 𝟙 (Φ.functor.obj U.right) := sorry

end compProjIso

/-- Whiskering the target-projection comparison by a target functor gives the canonical
comparison between the corresponding structured-arrow diagrams. -/
@[stacks 05T5 "diagram comparison for a localizer-morphism structured-arrow functor"]
noncomputable def diagramIso (Φ : LocalizerMorphism W₁ W₂) (X : C₁) (F : C₂ ⥤ D) :
    (Φ.structuredArrow X ⋙
        StructuredArrow.proj (W₂.Q.obj (Φ.functor.obj X)) W₂.Q) ⋙ F ≅
      (StructuredArrow.proj (W₁.Q.obj X) W₁.Q ⋙ Φ.functor) ⋙ F :=
  Functor.isoWhiskerRight (compProjIso Φ X) F

namespace diagramIso

/-- The forward structured-arrow diagram comparison has identity components. -/
@[simp]
theorem hom_app (Φ : LocalizerMorphism W₁ W₂) (X : C₁) (F : C₂ ⥤ D)
    (U : StructuredArrow (W₁.Q.obj X) W₁.Q) :
    (diagramIso Φ X F).hom.app U = 𝟙 (F.obj (Φ.functor.obj U.right)) := sorry

/-- The inverse structured-arrow diagram comparison has identity components. -/
@[simp]
theorem inv_app (Φ : LocalizerMorphism W₁ W₂) (X : C₁) (F : C₂ ⥤ D)
    (U : StructuredArrow (W₁.Q.obj X) W₁.Q) :
    (diagramIso Φ X F).inv.app U = 𝟙 (F.obj (Φ.functor.obj U.right)) := sorry

end diagramIso

/-- Transport the structured-arrow projection comparison across an arbitrary functor-level
comparison `Φ.functor ⋙ F₂ ≅ F₁ ⋙ G`.  This is the formal dual of the costructured-arrow
construction. -/
@[stacks 05T5 "functor-level diagram comparison for a structured-arrow functor"]
noncomputable def diagramIsoOfIso (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    {D₁ : Type u₃} {D₂ : Type u₄} [Category.{v₃} D₁] [Category.{v₄} D₂]
    {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} {G : D₁ ⥤ D₂}
    (e : Φ.functor ⋙ F₂ ≅ F₁ ⋙ G) :
    Φ.structuredArrow X ⋙
        (StructuredArrow.proj (W₂.Q.obj (Φ.functor.obj X)) W₂.Q ⋙ F₂) ≅
      (StructuredArrow.proj (W₁.Q.obj X) W₁.Q ⋙ F₁) ⋙ G :=
  (Functor.associator (Φ.structuredArrow X)
      (StructuredArrow.proj (W₂.Q.obj (Φ.functor.obj X)) W₂.Q) F₂).symm ≪≫
    diagramIso Φ X F₂ ≪≫
    Functor.associator (StructuredArrow.proj (W₁.Q.obj X) W₁.Q) Φ.functor F₂ ≪≫
    Functor.isoWhiskerLeft (StructuredArrow.proj (W₁.Q.obj X) W₁.Q) e ≪≫
    (Functor.associator (StructuredArrow.proj (W₁.Q.obj X) W₁.Q) F₁ G).symm

namespace diagramIsoOfIso

/-- The forward functor-level structured-arrow comparison is computed pointwise by `e.hom`. -/
@[simp]
theorem hom_app (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    {D₁ : Type u₃} {D₂ : Type u₄} [Category.{v₃} D₁] [Category.{v₄} D₂]
    {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} {G : D₁ ⥤ D₂}
    (e : Φ.functor ⋙ F₂ ≅ F₁ ⋙ G)
    (U : StructuredArrow (W₁.Q.obj X) W₁.Q) :
    (diagramIsoOfIso Φ X e).hom.app U = e.hom.app U.right := sorry

/-- The inverse functor-level structured-arrow comparison is computed pointwise by `e.inv`. -/
@[simp]
theorem inv_app (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    {D₁ : Type u₃} {D₂ : Type u₄} [Category.{v₃} D₁] [Category.{v₄} D₂]
    {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} {G : D₁ ⥤ D₂}
    (e : Φ.functor ⋙ F₂ ≅ F₁ ⋙ G)
    (U : StructuredArrow (W₁.Q.obj X) W₁.Q) :
    (diagramIsoOfIso Φ X e).inv.app U = e.inv.app U.right := sorry

end diagramIsoOfIso

end structuredArrow



end CategoryTheory.LocalizerMorphism
