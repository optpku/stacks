module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.SmallSheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Ringed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SectionsComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesHom

/-! # The comparison of fppf and étale ringed topoi -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open RingedSite RingedSite.ToposHom
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Fppf

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Forgetting the ring structure of a sheaf on the big fppf slice preserves the sheaf condition. -/
instance hasSheafCompose_overFppfTopology_forget_ringCat :
    (overFppfTopology X).HasSheafCompose (forget RingCat.{u}) := by
  sorry

/-- Restriction from the big fppf site commutes with forgetting coefficients. -/
def spacesRingedComparison_forgetIso :
    (spacesEtaleToBig X).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X) (overFppfTopology X) ⋙
      sheafCompose (spacesEtaleTopology X) (forget RingCat.{u}) ≅
    sheafCompose (overFppfTopology X) (forget RingCat.{u}) ⋙
      (SmallCoefficients.spacesComparison X).pushforward :=
  eqToIso (Functor.sheafPushforwardContinuous.compSheafCompose
    (spacesEtaleToBig X) (forget RingCat.{u})
    (spacesEtaleTopology X) (overFppfTopology X))

/-- Evaluation on an étale object followed by atlas descent compares its two section presentations. -/
def spacesRingedComparison_sectionMap (V : (spacesEtaleSite X)ᵒᵖ) :
    (spacesStructureSheaf X).obj.obj V ⟶
      (((spacesEtaleToBig X).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X) (overFppfTopology X)).obj
          (overFppfStructureSheaf X)).obj.obj V :=
  Etale.Big.spacesStructureToGamma V.unop ≫
    (Etale.Big.gammaGlobalSectionsIso V.unop.left).hom ≫
    (Functor.sheafPushforwardContinuousObjObjIso (spacesEtaleToBig X) RingCat.{u}
      (overFppfStructureSheaf X) V.unop).inv

/-- The canonical comparisons of sections commute with every restriction. -/
theorem spacesRingedComparison_structureSheafMap_naturality
    {V W : (spacesEtaleSite X)ᵒᵖ} (f : V ⟶ W) :
    (spacesStructureSheaf X).obj.map f ≫ spacesRingedComparison_sectionMap X W =
      spacesRingedComparison_sectionMap X V ≫
        (((spacesEtaleToBig X).sheafPushforwardContinuous RingCat.{u}
          (spacesEtaleTopology X) (overFppfTopology X)).obj
            (overFppfStructureSheaf X)).obj.map f := by
  sorry

/-- The direct-image structure map is the canonical global-section comparison on each étale object. -/
def spacesRingedComparison_structureSheafMap :
    (spacesRingedSite X).structureSheaf ⟶
      ((spacesEtaleToBig X).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X) (overFppfTopology X)).obj
          (overFppfRingedSite X).structureSheaf :=
  ObjectProperty.homMk
    { app := spacesRingedComparison_sectionMap X
      naturality := fun _ _ f ↦ spacesRingedComparison_structureSheafMap_naturality X f }

/-- The canonical global-section comparison respects the internal ring operations. -/
theorem spacesRingedComparison_isRingCompatible :
    @Direct.IsRingCompatible (overFppfRingedSite X) (spacesRingedSite X) _ _
      (SmallCoefficients.spacesComparison X)
      ((spacesEtaleToBig X).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X) (overFppfTopology X))
      (spacesRingedComparison_forgetIso X) (spacesRingedComparison_structureSheafMap X) := by
  sorry

/-- The canonical morphism from the big fppf ringed topos to the spaces-étale ringed topos. -/
def spacesRingedComparison : ToposHom (overFppfRingedSite X) (spacesRingedSite X) :=
  @ofDirectImage (overFppfRingedSite X) (spacesRingedSite X) _ _
    (SmallCoefficients.spacesComparison X)
    ((spacesEtaleToBig X).sheafPushforwardContinuous RingCat.{u}
      (spacesEtaleTopology X) (overFppfTopology X))
    (spacesRingedComparison_forgetIso X) (spacesRingedComparison_structureSheafMap X)
    (spacesRingedComparison_isRingCompatible X)

/-- The underlying topos morphism is the small-coefficient fppf-to-étale comparison. -/
theorem spacesRingedComparison_toTopos :
    (spacesRingedComparison X).toTopos = SmallCoefficients.spacesComparison X := rfl

end AlgebraicGeometry.AlgebraicSpace.Fppf
