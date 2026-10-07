module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import stacks_project.Chap85.Lemma_85_3_5

/-!
# Ringed stage inclusions and simplex operators

The total ringed site `(Sh(C_total), O)`, the degree-`n` ringed site `(Sh(C_n), O_n)`,
the morphism of ringed topoi `g_n`, and the morphisms `f_φ` attached to simplex operators.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})

/-- The total ringed site `(Sh(C_total), O)`. -/
abbrev totalRingedSite : RingedSite.{u, v, w} :=
  ofRingSheaf (topology C J) O

/-- The structure sheaf of `totalRingedSite C J O` is `O`. -/
theorem totalRingedSite_structureSheaf :
    (totalRingedSite C J O).structureSheaf = O :=
  sorry

/-- The ring sheaf `O_n` on `C.obj n`, the continuous inverse image of `O` along
`ofStage C n`. -/
abbrev componentRingSheaf (n : SimplexCategory) : Sheaf (J n).toGrothendieck RingCat.{w} :=
  Cocontinuous.inverseImageRingSheaf (ofStage C n) O

/-- `componentRingSheaf` is inverse image of `O` along `ofStage C n`. -/
theorem componentRingSheaf_eq (n : SimplexCategory) :
    componentRingSheaf C J O n = Cocontinuous.inverseImageRingSheaf (ofStage C n) O :=
  sorry

/-- The degree-`n` ringed site `(Sh(C_n), O_n)`. -/
abbrev componentRingedSite (n : SimplexCategory) : RingedSite.{u, v, w} :=
  ofRingSheaf (J n).toGrothendieck (componentRingSheaf C J O n)

/-- The structure sheaf of `componentRingedSite C J O n` is `O_n`. -/
theorem componentRingedSite_structureSheaf (n : SimplexCategory) :
    (componentRingedSite C J O n).structureSheaf = componentRingSheaf C J O n :=
  sorry

variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]

/-- The identity comparison `(ofStage C n).op ⋙ O ⟶ componentRingSheaf C J O n`
from which the structure map of `g_n` is obtained, so `g_n⁻¹ O = O_n`. -/
def stageIdentityComparison (n : SimplexCategory) :
    (ofStage C n).op ⋙ (totalRingedSite C J O).structureSheaf.obj ⟶
      (componentRingedSite C J O n).structureSheaf.obj :=
  𝟙 ((ofStage C n).op ⋙ O.obj)

/-- `stageIdentityComparison` is the identity on the restricted structure sheaf. -/
theorem stageIdentityComparison_eq_id (n : SimplexCategory) :
    stageIdentityComparison C J O n = 𝟙 ((ofStage C n).op ⋙ O.obj) :=
  sorry

/-- The morphism of ringed topoi `g_n : (Sh(C_n), O_n) ⟶ (Sh(C_total), O)` induced by
the continuous and cocontinuous inclusion `ofStage C n`, with identity structure map
so that `g_n⁻¹ O = O_n`. -/
def stageMorphism (n : SimplexCategory) :
    ToposHom (componentRingedSite C J O n) (totalRingedSite C J O) :=
  Cocontinuous.toRingedTopos (ofStage C n) (stageIdentityComparison C J O n)

/-- The underlying topos morphism of `stageMorphism C J O n` is `ofStageMorphism C J n`. -/
theorem stageMorphism_toTopos (n : SimplexCategory) :
    (stageMorphism C J O n).toTopos = ofStageMorphism C J n :=
  sorry

/-- Direct-image form of `O(φ)`: restriction of `O` along `stageInclusionWhisker` yields
`O_m ⟶ (u_φ)_* O_n`. -/
def ringedToposMapDirectStructure {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentRingedSite C J O m).structureSheaf ⟶
      ((C.map φ).toFunctor.sheafPushforwardContinuous RingCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck).obj
        (componentRingedSite C J O n).structureSheaf :=
  (sheafPushforwardContinuousNatTrans (stageInclusionWhisker C φ) RingCat.{w}
      (J m).toGrothendieck (topology C J)).app O ≫
    (sheafPushforwardContinuousComp (C.map φ).toFunctor (ofStage C n) RingCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck (topology C J)).inv.app O

/-- Coefficient-forgetful comparison for continuous ring-valued pushforward along `u_φ`. -/
def ringedToposMapForgetIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (C.map φ).toFunctor.sheafPushforwardContinuous RingCat.{w}
          (J m).toGrothendieck (J n).toGrothendieck ⋙
        sheafCompose (J m).toGrothendieck (forget RingCat.{w}) ≅
      sheafCompose (J n).toGrothendieck (forget RingCat.{w}) ⋙
        (C.map φ).toFunctor.sheafPushforwardContinuous (Type w)
          (J m).toGrothendieck (J n).toGrothendieck :=
  NatIso.ofComponents
    (fun P ↦
      (fullyFaithfulSheafToPresheaf (J m).toGrothendieck (Type w)).preimageIso
        (Functor.associator ((C.map φ).toFunctor.op) P.obj (forget RingCat.{w})))
    sorry

/-- Ring-compatibility of the direct-image presentation of `O(φ)`. -/
theorem ringedToposMap_isRingCompatible {m n : SimplexCategory} (φ : m ⟶ n) :
    @ToposHom.Direct.IsRingCompatible
      (componentRingedSite C J O n) (componentRingedSite C J O m) _ _
      ((C.map φ).toFunctor.morphismOfTopoiInOfContinuous
        (J m).toGrothendieck (J n).toGrothendieck)
      ((C.map φ).toFunctor.sheafPushforwardContinuous RingCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck)
      (ringedToposMapForgetIso C J φ) (ringedToposMapDirectStructure C J O φ) :=
  sorry

/-- The morphism of ringed topoi `f_φ : (Sh(C_n), O_n) ⟶ (Sh(C_m), O_m)` with underlying
topos morphism `toposMap C J φ` and structure map `O(φ) : f_φ⁻¹ O_m ⟶ O_n`. -/
def ringedToposMap {m n : SimplexCategory} (φ : m ⟶ n) :
    ToposHom (componentRingedSite C J O n) (componentRingedSite C J O m) :=
  @ToposHom.ofDirectImage (componentRingedSite C J O n) (componentRingedSite C J O m) _ _
    ((C.map φ).toFunctor.morphismOfTopoiInOfContinuous
      (J m).toGrothendieck (J n).toGrothendieck)
    ((C.map φ).toFunctor.sheafPushforwardContinuous RingCat.{w}
      (J m).toGrothendieck (J n).toGrothendieck)
    (ringedToposMapForgetIso C J φ) (ringedToposMapDirectStructure C J O φ)
    (ringedToposMap_isRingCompatible C J O φ)

/-- The underlying topos morphism of `ringedToposMap C J O φ` is `toposMap C J φ`. -/
theorem ringedToposMap_toTopos {m n : SimplexCategory} (φ : m ⟶ n) :
    (ringedToposMap C J O φ).toTopos = toposMap C J φ :=
  sorry

end CategoryTheory.SimplicialSites
