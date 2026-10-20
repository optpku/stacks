module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic

/-! # Formal glueing for closed-supported derived modules -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- If a morphism is an isomorphism over a closed subspace and is flat along its
inverse image, the derived pullback-pushforward counit is invertible on every
quasi-coherent complex supported on that inverse image. -/
theorem derivedPullback_pushforward_counit_isIso {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)]
    (hf : ∀ x : Points Y, x ∈ pointsImage (inverseImageι f i) → FlatAt f x)
    (Q : DerivedQCoh Y)
    (hQ : ModuleDerived.IsSupportedOn Q.obj (pointsImage (inverseImageι f i))) :
    IsIso ((Modules.derivedPullbackPushforwardAdjunction f).counit.app Q.obj) :=
  sorry

namespace SupportedOn

open CategoryTheory.ObjectProperty

/-- Derived pullback along `f` sends complexes supported on `|Z|` to complexes
supported on `|f⁻¹Z|`. -/
theorem pullback_mapsTo {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    quasiCoherentSupportedOn X (pointsImage i) ≤
      (quasiCoherentSupportedOn Y (pointsImage (inverseImageι f i))).inverseImage
        (Functor.LeftDerived.Homotopy.functor (Modules.pullback f)) :=
  sorry

/-- Derived pushforward along a quasi-compact quasi-separated morphism sends
complexes supported on `|f⁻¹Z|` to complexes supported on `|Z|`. -/
theorem pushforward_mapsTo {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    quasiCoherentSupportedOn Y (pointsImage (inverseImageι f i)) ≤
      (quasiCoherentSupportedOn X (pointsImage i)).inverseImage
        (Modules.moduleDerivedPushforward f) :=
  sorry

/-- Restricted derived pullback `Lf^*` on `D_{QCoh, |Z|}(𝒪_X)`. -/
noncomputable def pullback {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    SupportedOn X (pointsImage i) ⥤
      SupportedOn Y (pointsImage (inverseImageι f i)) :=
  FullSubcategory.restrict (Functor.LeftDerived.Homotopy.functor (Modules.pullback f))
    (pullback_mapsTo f i)

/-- Restricted derived pushforward `Rf_*` on `D_{QCoh, |f⁻¹Z|}(𝒪_Y)`. -/
noncomputable def pushforward {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    SupportedOn Y (pointsImage (inverseImageι f i)) ⥤
      SupportedOn X (pointsImage i) :=
  FullSubcategory.restrict (Modules.moduleDerivedPushforward f) (pushforward_mapsTo f i)

/-- The underlying object of restricted derived pullback is ambient `Lf^*`. -/
@[simp]
theorem pullback_obj_obj {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] (K : SupportedOn X (pointsImage i)) :
    ((pullback f i).obj K).obj = (Functor.LeftDerived.Homotopy.functor (Modules.pullback f)).obj K.obj :=
  sorry

/-- The underlying object of restricted derived pushforward is ambient `Rf_*`. -/
@[simp]
theorem pushforward_obj_obj {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i]
    (K : SupportedOn Y (pointsImage (inverseImageι f i))) :
    ((pushforward f i).obj K).obj = (Modules.moduleDerivedPushforward f).obj K.obj :=
  sorry

/-- The restricted adjunction `Lf^* ⊣ Rf_*` on supported quasi-coherent complexes. -/
noncomputable def adjunction {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    pullback f i ⊣ pushforward f i :=
  FullSubcategory.adjunction (Functor.LeftDerived.Homotopy.functor (Modules.pullback f))
    (Modules.moduleDerivedPushforward f)
    (Modules.derivedPullbackPushforwardAdjunction f)
    (pullback_mapsTo f i) (pushforward_mapsTo f i)

/-- In formal glueing, derived pushforward induces an equivalence between the
quasi-coherent derived categories supported on the inverse image and on the
closed subspace. -/
@[stacks 0AFJ]
instance pushforward_isEquivalence {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (pushforward f i).IsEquivalence :=
  sorry

/-- In formal glueing, restricted derived pullback is a quasi-inverse of
restricted derived pushforward on supported quasi-coherent complexes. -/
@[stacks 0AFJ]
theorem pullback_isQuasiInverse {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (pushforward f i).IsQuasiInverse (pullback f i) :=
  sorry

end SupportedOn

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
