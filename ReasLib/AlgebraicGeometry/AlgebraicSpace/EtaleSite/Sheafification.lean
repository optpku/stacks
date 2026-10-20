/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback

/-! Sheafification computed on the small étale site of each actual scheme chart.
The coefficient universe is unchanged. All section data comes from Mathlib's
scheme-site sheafification, whose small affine basis is constructed explicitly. -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u a v

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.Sheafification
variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Compose a scheme étale over a chart with that chart. -/
def chartOver (U : smallEtaleSite X) (V : U.left.left.Etale) : Over S :=
  Over.mk (V.hom ≫ U.left.hom)

/-- The scheme map from a local étale chart to its base chart. -/
def chartProjection (U : smallEtaleSite X) (V : U.left.left.Etale) :
    chartOver U V ⟶ U.left := Over.homMk V.hom rfl

/-- Composed local charts are étale over the algebraic space. -/
theorem chartEtale (U : smallEtaleSite X) (V : U.left.left.Etale) :
    AlgebraicSpace.Etale ((ofOverFunctor S).map (chartProjection U V) ≫ U.hom) := sorry

/-- The local scheme étale site maps to the algebraic-space étale site. -/
def charts (U : smallEtaleSite X) : U.left.left.Etale ⥤ smallEtaleSite X where
  obj V := smallEtaleSite.mk ((ofOverFunctor S).map (chartProjection U V) ≫ U.hom) (chartEtale U V)
  map f := MorphismProperty.CostructuredArrow.homMk
    (Over.homMk f.left sorry) trivial sorry
  map_id := sorry
  map_comp := sorry

/-- The identity local chart maps to the original chart by the identity scheme map. -/
def identityChartIso (U : smallEtaleSite X) :
    (charts U).obj (Scheme.Etale.mk (𝟙 U.left.left)) ≅ U where
  hom := MorphismProperty.CostructuredArrow.homMk (Over.homMk (𝟙 _) sorry) trivial sorry
  inv := MorphismProperty.CostructuredArrow.homMk (Over.homMk (𝟙 _) sorry) trivial sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Pullback projections give the comparison of local chart functors. -/
def pullbackProjection {U V : smallEtaleSite X} (f : U ⟶ V) (W : V.left.left.Etale) :
    (charts U).obj ((Scheme.smallEtalePullback f.left.left).obj W) ⟶
      (charts V).obj W :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk (pullback.fst W.hom f.left.left) sorry) trivial sorry

/-- The identity chart maps to the pullback of the target identity chart. -/
def identityPullback {U V : smallEtaleSite X} (f : U ⟶ V) :
    Scheme.Etale.mk (𝟙 U.left.left) ⟶
      (Scheme.smallEtalePullback f.left.left).obj (Scheme.Etale.mk (𝟙 V.left.left)) :=
  MorphismProperty.Over.homMk (pullback.lift f.left.left (𝟙 _) sorry) sorry

/-- Restriction to local scheme charts preserves sheaves. -/
instance chartsContinuous (U : smallEtaleSite X) :
    (charts U).IsContinuous U.left.left.smallEtaleTopology (smallEtaleTopology X) := sorry

variable (A : Type a) [Category.{v} A]
variable [∀ (U : smallEtaleSite X), HasWeakSheafify U.left.left.smallEtaleTopology A]

/-- Local scheme-site sheafification of a presheaf on the algebraic-space site. -/
def localSheaf (P : (smallEtaleSite X)ᵒᵖ ⥤ A) (U : smallEtaleSite X) :
    Sheaf U.left.left.smallEtaleTopology A :=
  (presheafToSheaf U.left.left.smallEtaleTopology A).obj ((charts U).op ⋙ P)

/-- Restrict the local sheafification unit along the scheme pullback projections. -/
def restrictionUnit (P : (smallEtaleSite X)ᵒᵖ ⥤ A)
    {U V : smallEtaleSite X} (f : U ⟶ V) :
    (charts V).op ⋙ P ⟶
      (Scheme.smallEtalePullback f.left.left).op ⋙ (localSheaf A P U).obj where
  app W := P.map (pullbackProjection f W.unop).op ≫
    (CategoryTheory.toSheafify U.left.left.smallEtaleTopology ((charts U).op ⋙ P)).app
      (op ((Scheme.smallEtalePullback f.left.left).obj W.unop))
  naturality := sorry

/-- The genuine restriction map, descended by scheme-site sheafification. -/
def restrictionMap (P : (smallEtaleSite X)ᵒᵖ ⥤ A)
    {U V : smallEtaleSite X} (f : U ⟶ V) :
    (localSheaf A P V).obj.obj (op (Scheme.Etale.mk (𝟙 V.left.left))) ⟶
      (localSheaf A P U).obj.obj (op (Scheme.Etale.mk (𝟙 U.left.left))) :=
  (sheafifyLift V.left.left.smallEtaleTopology (restrictionUnit A P f)
      (Functor.op_comp_isSheaf (Scheme.smallEtalePullback f.left.left)
        V.left.left.smallEtaleTopology U.left.left.smallEtaleTopology (localSheaf A P U))).app
          (op (Scheme.Etale.mk (𝟙 V.left.left))) ≫
    (localSheaf A P U).obj.map (identityPullback f).op

/-- Explicit sheafification presheaf, evaluated on each chart's identity. -/
def presheaf (P : (smallEtaleSite X)ᵒᵖ ⥤ A) : (smallEtaleSite X)ᵒᵖ ⥤ A where
  obj U := (localSheaf A P U.unop).obj.obj (op (Scheme.Etale.mk (𝟙 U.unop.left.left)))
  map f := restrictionMap A P f.unop
  map_id := sorry
  map_comp := sorry

/-- The local scheme-site construction satisfies descent. -/
theorem isSheaf (P : (smallEtaleSite X)ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (smallEtaleTopology X) (presheaf A P) := sorry

/-- Object map for the actual sheafification. -/
def obj (P : (smallEtaleSite X)ᵒᵖ ⥤ A) : Sheaf (smallEtaleTopology X) A :=
  ⟨presheaf A P, isSheaf A P⟩

/-- Sheafification acts on maps using the actual local sheafification functors. -/
def map {P Q : (smallEtaleSite X)ᵒᵖ ⥤ A} (f : P ⟶ Q) : obj A P ⟶ obj A Q where
  hom :=
    { app := fun U ↦
        ((presheafToSheaf U.unop.left.left.smallEtaleTopology A).map
          (Functor.whiskerLeft (charts U.unop).op f)).hom.app
            (op (Scheme.Etale.mk (𝟙 U.unop.left.left)))
      naturality := sorry }

/-- Concrete sheafification on the algebraic-space small étale site. -/
def functor : ((smallEtaleSite X)ᵒᵖ ⥤ A) ⥤ Sheaf (smallEtaleTopology X) A where
  obj := obj A
  map := map A
  map_id := sorry
  map_comp := sorry

/-- Its unit is the actual local sheafification unit. -/
def unit : 𝟭 ((smallEtaleSite X)ᵒᵖ ⥤ A) ⟶
    functor A ⋙ sheafToPresheaf (smallEtaleTopology X) A where
  app P :=
    { app := fun U ↦ P.map (identityChartIso U.unop).hom.op ≫
        (CategoryTheory.toSheafify U.unop.left.left.smallEtaleTopology
          ((charts U.unop).op ⋙ P)).app (op (Scheme.Etale.mk (𝟙 U.unop.left.left)))
      naturality := sorry }
  naturality := sorry

/-- Its counit descends the identity map to an existing sheaf locally. -/
def counit : sheafToPresheaf (smallEtaleTopology X) A ⋙ functor A ⟶
    𝟭 (Sheaf (smallEtaleTopology X) A) where
  app F :=
    { hom :=
        { app := fun U ↦
            (sheafifyLift U.unop.left.left.smallEtaleTopology
              (𝟙 ((charts U.unop).op ⋙ F.obj))
              (Functor.op_comp_isSheaf (charts U.unop)
                U.unop.left.left.smallEtaleTopology (smallEtaleTopology X) F)).app
                  (op (Scheme.Etale.mk (𝟙 U.unop.left.left))) ≫
              F.obj.map (identityChartIso U.unop).inv.op
          naturality := sorry } }
  naturality := sorry

/-- The sheafification adjunction records concrete unit and counit maps. -/
def adjunction : functor A ⊣ sheafToPresheaf (smallEtaleTopology X) A where
  unit := unit A
  counit := counit A
  left_triangle_components := sorry
  right_triangle_components := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale.Sheafification
