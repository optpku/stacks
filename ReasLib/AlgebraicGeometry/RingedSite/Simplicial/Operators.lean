module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Flat
public import ReasLib.CategoryTheory.Sites.Simplicial.LowerShriek

/-!
# Ringed stage inclusions and simplex operators

The total ringed site `(Sh(C_total), O)`, the degree-`n` ringed site `(Sh(C_n), O_n)`,
the morphism of ringed topoi `g_n`, and the morphisms `f_φ` attached to simplex operators.
-/

-- Private law proofs supply the proof fields of the explicit public constructions.
set_option backward.privateInPublic true

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

variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]

/-- The underlying topos morphism of `stageMorphism C J O n` is `ofStageMorphism C J n`. -/
theorem stageMorphism_toTopos (n : SimplexCategory) :
    (stageMorphism C J O n).toTopos = ofStageMorphism C J n := rfl

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

/-- Forgetting the ring structure commutes naturally with continuous pushforward. -/
private theorem ringedToposMapForgetIso_naturality {m n : SimplexCategory} (φ : m ⟶ n) :
    let F := (C.map φ).toFunctor.sheafPushforwardContinuous RingCat.{w}
      (J m).toGrothendieck (J n).toGrothendieck ⋙
        sheafCompose (J m).toGrothendieck (forget RingCat.{w})
    let G := sheafCompose (J n).toGrothendieck (forget RingCat.{w}) ⋙
      (C.map φ).toFunctor.sheafPushforwardContinuous (Type w)
        (J m).toGrothendieck (J n).toGrothendieck
    let e : ∀ P, F.obj P ≅ G.obj P := (fun P ↦
      (fullyFaithfulSheafToPresheaf (J m).toGrothendieck (Type w)).preimageIso
        (Functor.associator ((C.map φ).toFunctor.op) P.obj (forget RingCat.{w})))
    ∀ {P Q} (f : P ⟶ Q), F.map f ≫ (e Q).hom = (e P).hom ≫ G.map f := by
  sorry

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
    (ringedToposMapForgetIso_naturality C J φ)

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
    (ringedToposMap C J O φ).toTopos = toposMap C J φ := rfl

end CategoryTheory.SimplicialSites
