module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage.Complex
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
open ComplexShape

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Etale.HigherDirectImage.Complex

/-- Canonical identity comparison for the small étale pullback functor. -/
def siteIdentityIso (S : Scheme.{u}) : smallEtalePullback (𝟙 S) ≅ 𝟭 S.Etale :=
  conjugateIsoEquiv
    (MorphismProperty.Over.mapPullbackAdj (P := @Etale) (Q := ⊤)
      (𝟙 S) (by infer_instance) trivial)
    (Adjunction.id (C := S.Etale))
    (MorphismProperty.Over.mapId (P := @Etale) ⊤ S).symm

section Values

variable {T U : Scheme.{u}} (f : U ⟶ T)
variable [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
variable [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
    T.smallEtaleTopology U.smallEtaleTopology).Additive]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        T.smallEtaleTopology U.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]

/-- The higher direct image of a complex is homology of its total derived pushforward. -/
theorem value_obj
    (K : CochainComplex (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) ℤ) (p : ℤ) :
    value f K p =
      (DerivedCategory.homologyFunctor (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) p).obj
        ((etaleAbelianPushforwardDerived f).obj (DerivedCategory.Q.obj K)) := rfl

end Values

variable [∀ {S X : Scheme.{u}} (f : X ⟶ S),
  ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
    S.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]

/-- Identity inverse image of abelian étale sheaves is identified through the chosen adjunction. -/
def inverseImageIdIso (S : Scheme.{u}) :
    (smallEtalePullback (𝟙 S)).sheafPullback AddCommGrpCat.{u}
      S.smallEtaleTopology S.smallEtaleTopology ≅ 𝟭 _ :=
  Adjunction.leftAdjointIdIso
    ((smallEtalePullback (𝟙 S)).sheafAdjunctionContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology S.smallEtaleTopology)
    (Functor.sheafPushforwardContinuousId' (siteIdentityIso S) AddCommGrpCat.{u}
      S.smallEtaleTopology)

/-- Termwise identity inverse image of a cochain complex has its canonical identity comparison. -/
def inverseImageComplexIdIso (S : Scheme.{u}) :
    ((smallEtalePullback (𝟙 S)).sheafPullback AddCommGrpCat.{u}
      S.smallEtaleTopology S.smallEtaleTopology).mapHomologicalComplex (ComplexShape.up ℤ) ≅
        𝟭 _ :=
  NatIso.mapHomologicalComplex (inverseImageIdIso S) (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)

section IdentityLaw

variable {S X : Scheme.{u}} (f : X ⟶ S)
variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
  (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
  (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {T U : Scheme.{u}} (m : U ⟶ T)
    (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}), (smallEtalePullback m).op.HasLeftKanExtension G]
variable [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
  S.smallEtaleTopology X.smallEtaleTopology).Additive]
variable [Functor.HasRightDerivedFunctor
  (Functor.RightDerived.Cochain.toDerived
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology X.smallEtaleTopology))
  (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/-- Base change for the identity square agrees with the canonical identity pullback maps. -/
theorem baseChange_id
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ) (p : ℤ) :
    baseChange f f (𝟙 X) (𝟙 S) (by simp) K p ≫
      map f ((inverseImageComplexIdIso X).hom.app K) p =
        (inverseImageIdIso S).hom.app (value f K p) := sorry

end IdentityLaw


section Squares

variable {S X S' X' : Scheme.{u}}
variable (vertical : X ⟶ S) (vertical' : X' ⟶ S')
variable (top : X' ⟶ X) (bottom : S' ⟶ S)
variable (comm : top ≫ vertical = vertical' ≫ bottom)
variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify S'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf S'.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf S'.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {T U : Scheme.{u}} (morphism : U ⟶ T)
    (presheaf : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback morphism).op.HasLeftKanExtension presheaf]
variable [((smallEtalePullback vertical).sheafPushforwardContinuous AddCommGrpCat.{u}
    S.smallEtaleTopology X.smallEtaleTopology).Additive]
variable [((smallEtalePullback vertical').sheafPushforwardContinuous AddCommGrpCat.{u}
    S'.smallEtaleTopology X'.smallEtaleTopology).Additive]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback vertical).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology X.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback vertical').sheafPushforwardContinuous AddCommGrpCat.{u}
        S'.smallEtaleTopology X'.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u}) (up ℤ))]

/-- Canonical complex base change is natural in the cochain complex. -/
theorem baseChange_naturality
    {K L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ}
    (φ : K ⟶ L) (p : ℤ) :
    ((smallEtalePullback bottom).sheafPullback AddCommGrpCat.{u}
      S.smallEtaleTopology S'.smallEtaleTopology).map (map vertical φ p) ≫
        baseChange vertical vertical' top bottom comm L p =
      baseChange vertical vertical' top bottom comm K p ≫
        map vertical'
          (((smallEtalePullback top).sheafPullback AddCommGrpCat.{u}
            X.smallEtaleTopology X'.smallEtaleTopology).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.map φ) p := sorry

end Squares

section Squares
variable {S₀ X₀ S₁ X₁ S₂ X₂ : Scheme.{u}}
variable (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
variable (a : X₁ ⟶ X₀) (b : X₂ ⟶ X₁) (s : S₁ ⟶ S₀) (t : S₂ ⟶ S₁)
variable (h₁ : a ≫ f₀ = f₁ ≫ s) (h₂ : b ≫ f₁ = f₂ ≫ t)

variable [HasSheafify S₀.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify S₀.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
  (Sheaf S₀.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasSheafify X₀.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X₀.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
  (Sheaf X₀.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasSheafify S₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify S₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
  (Sheaf S₁.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasSheafify X₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
  (Sheaf X₁.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasSheafify S₂.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify S₂.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
  (Sheaf S₂.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasSheafify X₂.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X₂.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
  (Sheaf X₂.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {T U : Scheme.{u}} (m : U ⟶ T)
    (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}), (smallEtalePullback m).op.HasLeftKanExtension G]
variable [((smallEtalePullback f₀).sheafPushforwardContinuous AddCommGrpCat.{u}
  S₀.smallEtaleTopology X₀.smallEtaleTopology).Additive]
variable [Functor.HasRightDerivedFunctor
  (Functor.RightDerived.Cochain.toDerived
    ((smallEtalePullback f₀).sheafPushforwardContinuous AddCommGrpCat.{u}
      S₀.smallEtaleTopology X₀.smallEtaleTopology))
  (HomologicalComplex.quasiIso (Sheaf X₀.smallEtaleTopology AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback f₁).sheafPushforwardContinuous AddCommGrpCat.{u}
  S₁.smallEtaleTopology X₁.smallEtaleTopology).Additive]
variable [Functor.HasRightDerivedFunctor
  (Functor.RightDerived.Cochain.toDerived
    ((smallEtalePullback f₁).sheafPushforwardContinuous AddCommGrpCat.{u}
      S₁.smallEtaleTopology X₁.smallEtaleTopology))
  (HomologicalComplex.quasiIso (Sheaf X₁.smallEtaleTopology AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback f₂).sheafPushforwardContinuous AddCommGrpCat.{u}
  S₂.smallEtaleTopology X₂.smallEtaleTopology).Additive]
variable [Functor.HasRightDerivedFunctor
  (Functor.RightDerived.Cochain.toDerived
    ((smallEtalePullback f₂).sheafPushforwardContinuous AddCommGrpCat.{u}
      S₂.smallEtaleTopology X₂.smallEtaleTopology))
  (HomologicalComplex.quasiIso (Sheaf X₂.smallEtaleTopology AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/-- Successive canonical base changes agree with base change for the pasted square. -/
theorem baseChange_comp
    (K : CochainComplex (Sheaf X₀.smallEtaleTopology AddCommGrpCat.{u}) ℤ) (p : ℤ) :
    ((smallEtalePullback t).sheafPullback AddCommGrpCat.{u}
      S₁.smallEtaleTopology S₂.smallEtaleTopology).map
        (baseChange f₀ f₁ a s h₁ K p) ≫
      baseChange f₁ f₂ b t h₂
        (((smallEtalePullback a).sheafPullback AddCommGrpCat.{u}
          X₀.smallEtaleTopology X₁.smallEtaleTopology).mapHomologicalComplex
            (ComplexShape.up ℤ) |>.obj K) p ≫
      map f₂ ((NatIso.mapHomologicalComplex (HigherDirectImage.inverseImageCompIso b a)
        (ComplexShape.up ℤ)).hom.app K) p =
    (HigherDirectImage.inverseImageCompIso t s).hom.app (value f₀ K p) ≫
      baseChange f₀ f₂ (b ≫ a) (t ≫ s)
        (by rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]) K p := sorry

end Squares

end AlgebraicGeometry.Scheme.Etale.HigherDirectImage.Complex
