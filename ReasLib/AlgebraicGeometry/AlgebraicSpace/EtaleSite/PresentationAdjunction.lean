module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ExtensionComparison

/-!
# Étale restriction of type sheaves and geometric inverse image

Restriction has actual section maps for its unit and graph evaluation for its counit.
The full chart lift is used only for sheaves, with the genuine small-chart extension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleTopos

variable {S : Scheme.{u}}

/-- The type-valued restriction diagram at an actual base-change object. -/
abbrev restrictTypeDiagram {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (F : Sheaf (smallEtaleTopology X) (Type u)) (V : smallEtaleSite X) :=
  StructuredArrow.proj (op ((etaleBaseChange p).obj V)) (smallEtaleToSpaces U).op ⋙
    (((restrictPostcompose p).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology U) (smallEtaleTopology X)).obj F).obj

/-- The unit cone consists of the actual restriction maps of a type sheaf. -/
def restrictTypeUnitCone {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (F : Sheaf (smallEtaleTopology X) (Type u)) (V : smallEtaleSite X) :
    Cone (restrictTypeDiagram p F V) where
  pt := F.obj.obj (op V)
  π :=
    { app := fun a ↦ F.obj.map
        (op (restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p V a)))
      naturality := sorry }

/-- The actual full-chart lift assembles the restriction maps into the unit. -/
def restrictTypeUnit {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    𝟭 (Sheaf (smallEtaleTopology X) (Type u)) ⟶
      (restrictPostcompose p).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology U) (smallEtaleTopology X) ⋙ typePushforward p where
  app F :=
    ⟨{ app := fun V ↦
        EtaleTopos.allChartLift U
          (((restrictPostcompose p).sheafPushforwardContinuous (Type u)
            (smallEtaleTopology U) (smallEtaleTopology X)).obj F)
          ((etaleBaseChange p).obj V.unop) (restrictTypeUnitCone p F V.unop)
       naturality := sorry }⟩
  naturality := sorry

/-- The counit evaluates the actual extended sheaf at the graph of its chart. -/
def restrictTypeCounit {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    typePushforward p ⋙
      (restrictPostcompose p).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology U) (smallEtaleTopology X) ⟶
      𝟭 (Sheaf (smallEtaleTopology U) (Type u)) where
  app F :=
    ⟨{ app := fun V ↦
        EtaleTopos.extensionEvaluation U F (restrictGraphOver p V.unop)
       naturality := sorry }⟩
  naturality := sorry

/-- Étale restriction is adjoint to the genuine small-chart direct image. -/
def restrictTypeAdjunction {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (restrictPostcompose p).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology U) (smallEtaleTopology X) ⊣ typePushforward p :=
  Adjunction.mkOfUnitCounit
    { unit := restrictTypeUnit p
      counit := restrictTypeCounit p
      left_triangle := sorry
      right_triangle := sorry }

/-- The adjunction unit is the actual lift of the restriction-map cone. -/
@[simp]
theorem restrictTypeAdjunction_unit {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (restrictTypeAdjunction p).unit = restrictTypeUnit p := rfl

/-- The adjunction counit is the actual graph-evaluation map. -/
@[simp]
theorem restrictTypeAdjunction_counit {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (restrictTypeAdjunction p).counit = restrictTypeCounit p := rfl

/-- Étale restriction is inverse image by uniqueness of these actual left adjoints. -/
def restrictTypeIsoInverseImage {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (restrictPostcompose p).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology U) (smallEtaleTopology X) ≅
      (morphismOfTopoi p).inverseImage :=
  (restrictTypeAdjunction p).leftAdjointUniq (morphismOfTopoi p).adjunction

end AlgebraicGeometry.AlgebraicSpace.EtaleTopos
