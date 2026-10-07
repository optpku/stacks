module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction
public import stacks_project.Chap81.Lemma_81_10_10_SupportedOn
public import stacks_project.Chap81.Lemma_81_10_5_Adjunction
public import stacks_project.Chap81.Situation_81_10_6_FormalGlueing

/-!
# Restricted derived pullback and pushforward on supported quasi-coherent complexes

In the formal-glueing situation, `Lf^*` and `Rf_*` restrict to the full
subcategories `D_{QCoh, |Z|}(𝒪_X)` and `D_{QCoh, |f⁻¹Z|}(𝒪_Y)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn

/-- Derived pullback along `f` sends complexes supported on `|Z|` to complexes
supported on `|f⁻¹Z|`. -/
theorem pullback_mapsTo {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    quasiCoherentSupportedOn X (pointsImage i) ≤
      (quasiCoherentSupportedOn Y (pointsImage (inverseImageι f i))).inverseImage
        (modulePullbackDerived f) :=
  sorry

/-- Derived pushforward along a quasi-compact quasi-separated morphism sends
complexes supported on `|f⁻¹Z|` to complexes supported on `|Z|`. -/
theorem pushforward_mapsTo {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    quasiCoherentSupportedOn Y (pointsImage (inverseImageι f i)) ≤
      (quasiCoherentSupportedOn X (pointsImage i)).inverseImage
        (Modules.pushforwardDerived f) :=
  sorry

/-- Restricted derived pullback `Lf^*` on `D_{QCoh, |Z|}(𝒪_X)`. -/
noncomputable def pullback {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    SupportedOn X (pointsImage i) ⥤
      SupportedOn Y (pointsImage (inverseImageι f i)) :=
  FullSubcategory.restrict (modulePullbackDerived f) (pullback_mapsTo f i)

/-- Restricted derived pushforward `Rf_*` on `D_{QCoh, |f⁻¹Z|}(𝒪_Y)`. -/
noncomputable def pushforward {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    SupportedOn Y (pointsImage (inverseImageι f i)) ⥤
      SupportedOn X (pointsImage i) :=
  FullSubcategory.restrict (Modules.pushforwardDerived f) (pushforward_mapsTo f i)

/-- The underlying object of restricted derived pullback is ambient `Lf^*`. -/
@[simp]
theorem pullback_obj_obj {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] (K : SupportedOn X (pointsImage i)) :
    ((pullback f i).obj K).obj = (modulePullbackDerived f).obj K.obj :=
  sorry

/-- The underlying object of restricted derived pushforward is ambient `Rf_*`. -/
@[simp]
theorem pushforward_obj_obj {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i]
    (K : SupportedOn Y (pointsImage (inverseImageι f i))) :
    ((pushforward f i).obj K).obj = (Modules.pushforwardDerived f).obj K.obj :=
  sorry

/-- The restricted adjunction `Lf^* ⊣ Rf_*` on supported quasi-coherent complexes. -/
noncomputable def adjunction {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    pullback f i ⊣ pushforward f i :=
  FullSubcategory.adjunction (modulePullbackDerived f) (Modules.pushforwardDerived f)
    (modulePullbackDerivedPushforwardAdjunction f)
    (pullback_mapsTo f i) (pushforward_mapsTo f i)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn
