module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Pro-étale base change of module sheaves

Base change of weakly étale objects along an arbitrary scheme morphism, and the
induced inverse image of sheaves of modules on small pro-étale sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {Y X : Scheme.{u}}

/-- Base change of the small pro-étale site along a scheme morphism. -/
def baseChange (f : Y ⟶ X) : X.ProEt ⥤ Y.ProEt :=
  MorphismProperty.Over.pullback @WeaklyEtale ⊤ f

/-- Pro-étale base change is `MorphismProperty.Over.pullback` along weakly étale morphisms. -/
theorem baseChange_def (f : Y ⟶ X) :
    baseChange f = MorphismProperty.Over.pullback @WeaklyEtale ⊤ f :=
  sorry

/-- Base change of weakly étale objects is continuous for the small pro-étale topologies. -/
instance baseChange_isContinuous (f : Y ⟶ X) :
    Functor.IsContinuous (baseChange f) (topology X) (topology Y) :=
  sorry

/-- Base change along a composite is isomorphic to the composite of the base-change functors. -/
def baseChange_comp {Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) :
    baseChange (g ≫ f) ≅ baseChange f ⋙ baseChange g :=
  MorphismProperty.Over.pullbackComp g f

/-- Base change along the identity is isomorphic to the identity functor. -/
def baseChange_id : baseChange (𝟙 X) ≅ 𝟭 X.ProEt :=
  conjugateIsoEquiv
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ (𝟙 X)
      (inferInstance : WeaklyEtale (𝟙 X)) trivial)
    Adjunction.id
    (MorphismProperty.Over.mapId (P := @WeaklyEtale) (Q := ⊤) X).symm

variable {Λ : Type w} [Ring Λ]

/-- Inverse image of sheaves of `Λ`-modules along a scheme morphism, induced by pro-étale
base change. -/
def modulePullback (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)] :
    Sheaf (topology X) (ModuleCat.{w} Λ) ⥤ Sheaf (topology Y) (ModuleCat.{w} Λ) :=
  (baseChange f).sheafPullback (ModuleCat.{w} Λ) (topology X) (topology Y)

/-- Module inverse image is sheaf pullback along pro-étale base change. -/
theorem modulePullback_def (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)] :
    modulePullback f =
      (baseChange f).sheafPullback (ModuleCat.{w} Λ) (topology X) (topology Y) :=
  sorry

/-- Inverse image of a module sheaf along a scheme morphism. -/
def moduleRestrict (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
    (F : Sheaf (topology X) (ModuleCat.{w} Λ)) :
    Sheaf (topology Y) (ModuleCat.{w} Λ) :=
  (modulePullback f).obj F

/-- `moduleRestrict` is the action of `modulePullback` on objects. -/
theorem moduleRestrict_def (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
    (F : Sheaf (topology X) (ModuleCat.{w} Λ)) :
    moduleRestrict f F = (modulePullback f).obj F :=
  sorry

/-- Inverse image along a composite morphism is isomorphic to the composite of the
inverse-image functors. -/
def modulePullback_comp {Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [∀ P : Y.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange g).op.HasLeftKanExtension P]
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange (g ≫ f)).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
    [HasWeakSheafify (topology Z) (ModuleCat.{w} Λ)] :
    (modulePullback (g ≫ f) :
        Sheaf (topology X) (ModuleCat.{w} Λ) ⥤
          Sheaf (topology Z) (ModuleCat.{w} Λ)) ≅
      (modulePullback f :
          Sheaf (topology X) (ModuleCat.{w} Λ) ⥤
            Sheaf (topology Y) (ModuleCat.{w} Λ)) ⋙
        (modulePullback g :
          Sheaf (topology Y) (ModuleCat.{w} Λ) ⥤
            Sheaf (topology Z) (ModuleCat.{w} Λ)) :=
  (Adjunction.leftAdjointCompIso
      ((baseChange f).sheafAdjunctionContinuous (ModuleCat.{w} Λ)
        (topology X) (topology Y))
      ((baseChange g).sheafAdjunctionContinuous (ModuleCat.{w} Λ)
        (topology Y) (topology Z))
      ((baseChange (g ≫ f)).sheafAdjunctionContinuous (ModuleCat.{w} Λ)
        (topology X) (topology Z))
      (Functor.sheafPushforwardContinuousComp' (baseChange_comp g f).symm
        (ModuleCat.{w} Λ) (topology X) (topology Y) (topology Z))).symm

/-- Inverse image along the identity is isomorphic to the identity functor. -/
def modulePullback_id
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange (𝟙 X)).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)] :
    modulePullback (𝟙 X) ≅ 𝟭 (Sheaf (topology X) (ModuleCat.{w} Λ)) :=
  Adjunction.leftAdjointIdIso
    ((baseChange (𝟙 X)).sheafAdjunctionContinuous (ModuleCat.{w} Λ)
      (topology X) (topology X))
    (Functor.sheafPushforwardContinuousId' baseChange_id
      (ModuleCat.{w} Λ) (topology X))

end AlgebraicGeometry.Scheme.ProEt
