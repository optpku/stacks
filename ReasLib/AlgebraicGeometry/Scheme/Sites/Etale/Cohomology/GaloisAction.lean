module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisAction
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImageStalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantPullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.DirectImage.BaseChange
public import ReasLib.CategoryTheory.Sites.Cohomology.SectionsComparison
public import ReasLib.CategoryTheory.Sites.Cohomology.Map
public import ReasLib.CategoryTheory.Sites.Point.Initial

/-!
# Galois action on geometric étale cohomology and higher-direct-image stalks

This leaf owns the `G_k`-module structures on `H^j(X_{k̄}, F|_{X_{k̄}})` and on
`(R^j α_* F)_{Spec(k̄)}` for a scheme `X` over `k`, using the pullback action of
`Spec(σ) × id_X` and precomposition of pointed étale lifts.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Small-étale pullback admits left Kan extensions of abelian presheaves. -/
instance smallEtalePullback_op_hasLeftKanExtension
    {S T : Scheme.{u}} (f : T ⟶ S) (G : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (smallEtalePullback f).op.HasLeftKanExtension G :=
  sorry

variable {k : Type u} [Field k]

/-- The small-étale point of `Spec k` determined by `Spec (AlgebraicClosure k)`. -/
abbrev specPointSmallEtale :
    ((Spec (CommRingCat.of k)).smallEtaleTopology).Point :=
  Scheme.pointSmallEtale (FieldExtension.specMap k (AlgebraicClosure k))

/-- `specPointSmallEtale` is the étale point associated to the structure map of
`AlgebraicClosure k`. -/
theorem specPointSmallEtale_spec :
    specPointSmallEtale =
      Scheme.pointSmallEtale (FieldExtension.specMap k (AlgebraicClosure k)) :=
  sorry

/-- The geometric point `Spec (AlgebraicClosure k) ⟶ Spec k`. -/
abbrev specGeometricPoint : Scheme.GeometricPoint (Spec (CommRingCat.of k)) :=
  Scheme.GeometricPoint.of (AlgebraicClosure k)
    (FieldExtension.specMap k (AlgebraicClosure k))

/-- The underlying morphism of `specGeometricPoint` is the field-extension spectrum map. -/
theorem specGeometricPoint_hom :
    (specGeometricPoint).hom =
      FieldExtension.specMap k (AlgebraicClosure k) :=
  sorry

/-- The automorphism of the geometric point `Spec (AlgebraicClosure k) ⟶ Spec k`
induced by a Galois element. -/
def specPointGaloisIso (σ : Gal(AlgebraicClosure k/k)) :
    Over.mk (FieldExtension.specMap k (AlgebraicClosure k)) ≅
      Over.mk (FieldExtension.specMap k (AlgebraicClosure k)) :=
  Over.isoMk
    { hom := FieldExtension.Galois.baseAut k (AlgebraicClosure k) σ
      inv := FieldExtension.Galois.baseAut k (AlgebraicClosure k) σ⁻¹
      hom_inv_id := sorry
      inv_hom_id := sorry }
    (FieldExtension.Galois.baseAut_over k (AlgebraicClosure k) σ)

/-- The underlying scheme automorphism of `specPointGaloisIso` is Galois `baseAut`. -/
theorem specPointGaloisIso_hom (σ : Gal(AlgebraicClosure k/k)) :
    (specPointGaloisIso σ).hom.left =
      FieldExtension.Galois.baseAut k (AlgebraicClosure k) σ :=
  sorry

variable (X : SchemeOverField k)
variable (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
variable (j : ℕ)

/-- Geometric étale cohomology `H^j(X_{k̄}, F|_{X_{k̄}})`. -/
def geometricEtaleCohomology : AddCommGrpCat.{u} :=
  ((etaleAbelianSheafPullback
      (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).obj F).H'
    j (globalEtale (FieldExtension.baseChange k (AlgebraicClosure k) X.hom))

/-- Unfolding of geometric étale cohomology as objectwise `H'` of the inverse image
along the projection `X_{k̄} ⟶ X`. -/
theorem geometricEtaleCohomology_spec :
    geometricEtaleCohomology X F j =
      ((etaleAbelianSheafPullback
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).obj F).H'
        j (globalEtale (FieldExtension.baseChange k (AlgebraicClosure k) X.hom)) :=
  sorry

/-- Coefficient identification `(Spec(σ) × id_X)^{-1} (F|_{X_{k̄}}) ≅ F|_{X_{k̄}}`
coming from `Galois.map σ ≫ toSource = toSource`. -/
def galoisPastingIso (σ : Gal(AlgebraicClosure k/k)) :
    (etaleAbelianSheafPullback
        (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)).obj
      ((etaleAbelianSheafPullback
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).obj F) ≅
      (etaleAbelianSheafPullback
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).obj F :=
  (HigherDirectImage.inverseImageCompIso
      (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)
      (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).app F ≪≫
    (eqToIso
      (congrArg
        (fun h : FieldExtension.baseChange k (AlgebraicClosure k) X.hom ⟶ X.left ↦
          etaleAbelianSheafPullback h)
        (FieldExtension.Galois.map_toSource k (AlgebraicClosure k) X.hom σ))).app F

/-- Unfolding of the Galois pasting isomorphism as composite pullback followed by
congruence along `Galois.map_toSource`. -/
theorem galoisPastingIso_spec (σ : Gal(AlgebraicClosure k/k)) :
    galoisPastingIso X F σ =
      (HigherDirectImage.inverseImageCompIso
          (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).app F ≪≫
        (eqToIso
          (congrArg
            (fun h : FieldExtension.baseChange k (AlgebraicClosure k) X.hom ⟶ X.left ↦
              etaleAbelianSheafPullback h)
            (FieldExtension.Galois.map_toSource k (AlgebraicClosure k) X.hom σ))).app F :=
  sorry

/-- The Galois action `σ · ξ := (Spec(σ) × id_X)^* ξ` on geometric étale cohomology. -/
def galoisAction_geometricEtaleCohomology (σ : Gal(AlgebraicClosure k/k)) :
    geometricEtaleCohomology X F j ⟶ geometricEtaleCohomology X F j :=
  cohomologyPullback
      (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)
      ((etaleAbelianSheafPullback
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).obj F) j ≫
    Sheaf.cohomologyMap (galoisPastingIso X F σ).hom j
      (globalEtale (FieldExtension.baseChange k (AlgebraicClosure k) X.hom))

/-- Unfolding of the geometric cohomology action as cohomology pullback followed by
the pasting identification of coefficients. -/
theorem galoisAction_geometricEtaleCohomology_spec (σ : Gal(AlgebraicClosure k/k)) :
    galoisAction_geometricEtaleCohomology X F j σ =
      cohomologyPullback
          (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)
          ((etaleAbelianSheafPullback
              (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).obj F) j ≫
        Sheaf.cohomologyMap (galoisPastingIso X F σ).hom j
          (globalEtale (FieldExtension.baseChange k (AlgebraicClosure k) X.hom)) :=
  sorry

/-- The `G_k`-module `H^j(X_{k̄}, F|_{X_{k̄}})`. -/
def geometricEtaleCohomologyGaloisModule :
    Action AddCommGrpCat.{u} Gal(AlgebraicClosure k/k) where
  V := geometricEtaleCohomology X F j
  ρ :=
    { toFun := fun σ ↦ galoisAction_geometricEtaleCohomology X F j σ
      map_one' := sorry
      map_mul' := sorry }

/-- The underlying additive group of the geometric cohomology Galois module. -/
theorem geometricEtaleCohomologyGaloisModule_V :
    (geometricEtaleCohomologyGaloisModule X F j).V =
      geometricEtaleCohomology X F j :=
  sorry

/-- Evaluating the geometric cohomology Galois module recovers the pullback action. -/
theorem geometricEtaleCohomologyGaloisModule_ρ (σ : Gal(AlgebraicClosure k/k)) :
    (geometricEtaleCohomologyGaloisModule X F j).ρ σ =
      galoisAction_geometricEtaleCohomology X F j σ :=
  sorry

/-- The stalk `(R^j α_* F)_{Spec(k̄)}` of the higher direct image along the structure
morphism `α = X.hom`. -/
def higherDirectImageStalk : AddCommGrpCat.{u} :=
  (specPointSmallEtale).sheafFiber.obj
    (Sheaf.higherDirectImage (smallEtalePullback X.hom) F j)

/-- Unfolding of the higher-direct-image stalk as the étale sheaf fiber at
`Spec (AlgebraicClosure k)`. -/
theorem higherDirectImageStalk_spec :
    higherDirectImageStalk X F j =
      (specPointSmallEtale).sheafFiber.obj
        (Sheaf.higherDirectImage (smallEtalePullback X.hom) F j) :=
  sorry

/-- Galois precomposition of pointed étale lifts commutes with restriction of sections
of the higher direct image. -/
theorem galoisAction_higherDirectImageStalk_compatible (σ : Gal(AlgebraicClosure k/k)) :
    ∀ ⦃U V : (Spec (CommRingCat.of k)).Etale⦄ (iUV : U ⟶ V)
      (x : (specPointSmallEtale).fiber.obj U),
      ((sheafToPresheaf (Spec (CommRingCat.of k)).smallEtaleTopology AddCommGrpCat.{u}).obj
            (Sheaf.higherDirectImage (smallEtalePullback X.hom) F j)).map iUV.op ≫
          (specPointSmallEtale).toPresheafFiber U
            ((geometricPointFiberMap (FieldExtension.specMap k (AlgebraicClosure k))
                (specPointGaloisIso σ)).app U x)
            (Sheaf.higherDirectImage (smallEtalePullback X.hom) F j).obj =
        (specPointSmallEtale).toPresheafFiber V
          ((geometricPointFiberMap (FieldExtension.specMap k (AlgebraicClosure k))
              (specPointGaloisIso σ)).app V
            ((specPointSmallEtale).fiber.map iUV x))
          (Sheaf.higherDirectImage (smallEtalePullback X.hom) F j).obj :=
  sorry

/-- The action on the higher-direct-image stalk induced by precomposition of pointed
étale lifts with a Galois automorphism. -/
def galoisAction_higherDirectImageStalk (σ : Gal(AlgebraicClosure k/k)) :
    higherDirectImageStalk X F j ⟶ higherDirectImageStalk X F j :=
  (specPointSmallEtale).presheafFiberDesc
    (fun U x ↦
      (specPointSmallEtale).toPresheafFiber U
        ((geometricPointFiberMap (FieldExtension.specMap k (AlgebraicClosure k))
            (specPointGaloisIso σ)).app U x)
        (Sheaf.higherDirectImage (smallEtalePullback X.hom) F j).obj)
    (galoisAction_higherDirectImageStalk_compatible X F j σ)

/-- On canonical stalk generators, the higher-direct-image Galois action is
precomposition of the pointed lift with `specPointGaloisIso`. -/
theorem galoisAction_higherDirectImageStalk_spec (σ : Gal(AlgebraicClosure k/k))
    (U : (Spec (CommRingCat.of k)).Etale)
    (x : (specPointSmallEtale).fiber.obj U) :
    (specPointSmallEtale).toPresheafFiber U x
        (Sheaf.higherDirectImage (smallEtalePullback X.hom) F j).obj ≫
      galoisAction_higherDirectImageStalk X F j σ =
      (specPointSmallEtale).toPresheafFiber U
        ((geometricPointFiberMap (FieldExtension.specMap k (AlgebraicClosure k))
            (specPointGaloisIso σ)).app U x)
        (Sheaf.higherDirectImage (smallEtalePullback X.hom) F j).obj :=
  sorry

/-- The `G_k`-module `(R^j α_* F)_{Spec(k̄)}` with its natural Galois action. -/
def higherDirectImageStalkGaloisModule :
    Action AddCommGrpCat.{u} Gal(AlgebraicClosure k/k) where
  V := higherDirectImageStalk X F j
  ρ :=
    { toFun := fun σ ↦ galoisAction_higherDirectImageStalk X F j σ
      map_one' := sorry
      map_mul' := sorry }

/-- The underlying additive group of the higher-direct-image stalk Galois module. -/
theorem higherDirectImageStalkGaloisModule_V :
    (higherDirectImageStalkGaloisModule X F j).V = higherDirectImageStalk X F j :=
  sorry

/-- Evaluating the stalk Galois module recovers the action by precomposition of pointed lifts. -/
theorem higherDirectImageStalkGaloisModule_ρ (σ : Gal(AlgebraicClosure k/k)) :
    (higherDirectImageStalkGaloisModule X F j).ρ σ =
      galoisAction_higherDirectImageStalk X F j σ :=
  sorry

/- Private implementation visibility justification: expose the concrete endpoint transport
body to the exported comparison without introducing a public name or an inference instance. -/
set_option backward.privateInPublic true in
/-- The fiber at the identity geometric point of the spectrum of a separably closed field
is the global sections functor on its small étale site. -/
private def identityPointSectionsIso (field : Type u) [Field field] [IsSepClosed field] :
    (Scheme.pointSmallEtale (𝟙 (Spec (.of field)))).sheafFiber (A := AddCommGrpCat.{u}) ≅
      siteAbelianSectionsFunctor (Spec (.of field)).smallEtaleTopology
        (globalEtale (Spec (.of field))) := by
  let point := Scheme.pointSmallEtale (𝟙 (Spec (.of field)))
  let lift : point.fiber.obj (globalEtale (Spec (.of field))) := 𝟙 _
  have initial : IsInitial (point.fiber.elementsMk _ lift) := by
    refine IsInitial.ofUniqueHom (fun neighborhood ↦ ?_) (fun neighborhood morphism ↦ ?_)
    · exact ⟨MorphismProperty.Over.homMk neighborhood.snd.left (Over.w neighborhood.snd),
        by
          apply Over.OverMorphism.ext
          change 𝟙 _ ≫ neighborhood.snd.left = neighborhood.snd.left
          simp⟩
    · apply Subtype.ext
      apply MorphismProperty.Over.Hom.ext
      have equality := congrArg Over.Hom.left morphism.property
      change 𝟙 _ ≫ morphism.val.left = neighborhood.snd.left at equality
      simpa using equality
  exact point.sheafFiberIsoOfInitial initial ≪≫
    (sheafSectionsNatIsoEvaluation
      (J := (Spec (.of field)).smallEtaleTopology) (A := AddCommGrpCat.{u})
      (X := globalEtale (Spec (.of field)))).symm

/- Private implementation visibility justification: expose the concrete endpoint transport
body to the exported comparison without introducing a public name or an inference instance. -/
set_option backward.privateInPublic true in
/-- Taking the identity geometric fiber of higher direct images to an algebraically closed
field identifies them with objectwise cohomology on the geometric scheme. -/
private def geometricHigherDirectImageFiberIso :
    ((smallEtalePullback (FieldExtension.toBase k (AlgebraicClosure k) X.hom)).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Spec (.of (AlgebraicClosure k))).smallEtaleTopology
        (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology).rightDerived j ⋙
      (Scheme.pointSmallEtale (𝟙 (Spec (.of (AlgebraicClosure k))))).sheafFiber ≅
    Sheaf.cohomologyAtObjectFunctor
      (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology
      (globalEtale (FieldExtension.baseChange k (AlgebraicClosure k) X.hom)) j :=
  let projection := FieldExtension.toBase k (AlgebraicClosure k) X.hom
  let point := Scheme.pointSmallEtale (𝟙 (Spec (.of (AlgebraicClosure k))))
  let pushforward := (smallEtalePullback projection).sheafPushforwardContinuous
    AddCommGrpCat.{u} (Spec (.of (AlgebraicClosure k))).smallEtaleTopology
    (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology
  let pointAdditive : point.sheafFiber.Additive :=
    Functor.additive_of_preserves_binary_products point.sheafFiber
  let fiberSectionsIso :=
    Functor.isoWhiskerLeft pushforward (identityPointSectionsIso (AlgebraicClosure k))
  let compositeAdditive := Functor.additive_of_iso fiberSectionsIso.symm
  (@Functor.RightDerived.postcompIso _ _ _ _ _ _ _ _ _ pushforward point.sheafFiber
    inferInstance pointAdditive inferInstance inferInstance j).symm ≪≫
    @NatIso.rightDerived _ _ _ _ _ _ _ _ _ compositeAdditive inferInstance
      fiberSectionsIso j ≪≫
    NatIso.rightDerived
      (SiteAbelianSectionsDerived.sectionsIso
        (JC := (Spec (.of (AlgebraicClosure k))).smallEtaleTopology)
        (JD := (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology)
        (smallEtalePullback projection) (globalEtale (Spec (.of (AlgebraicClosure k))))) j ≪≫
    NatIso.rightDerived
      ((sheafSections
        (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology
        AddCommGrpCat.{u}).mapIso (globalEtalePullbackIso projection).symm.op) j ≪≫
    (SiteAbelianSectionsDerived.heterogeneousRightDerivedSectionsIso
      (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology
      (globalEtale (FieldExtension.baseChange k (AlgebraicClosure k) X.hom)) j).symm

/- Private implementation visibility justification: the concrete comparison exports its body
while its one-use endpoint transports remain private; this changes no inference or assumptions. -/
set_option backward.privateInPublic true in
/-- The geometric-stalk comparison for a scheme over a field is ordinary higher-direct-image
base change followed by the canonical identification of derived sections with cohomology. -/
def higherDirectImageStalkComparison :
    higherDirectImageStalk X F j ⟶ geometricEtaleCohomology X F j :=
  let baseMap := FieldExtension.specMap k (AlgebraicClosure k)
  let projection := FieldExtension.toBase k (AlgebraicClosure k) X.hom
  let sourceMap := FieldExtension.toSource k (AlgebraicClosure k) X.hom
  let geometricPoint := GeometricPoint.of (AlgebraicClosure k)
    (𝟙 (Spec (.of (AlgebraicClosure k))))
  let point := GeometricPoint.toSmallEtalePoint geometricPoint
  let directImage := Sheaf.higherDirectImage (smallEtalePullback X.hom) F j
  let imagePointTransport := eqToIso (congrArg
    (fun hom : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) ↦
      (Scheme.pointSmallEtale hom).sheafFiber.obj directImage) (Category.id_comp baseMap))
  imagePointTransport.inv ≫
    (GrothendieckTopology.Point.Hom.sheafFiber (A := AddCommGrpCat.{u})
      ⟨smallEtaleInverseImage_comapFiberInv baseMap geometricPoint⟩).app directImage ≫
    (point.sheafFiberComapIsoOfMorphismOfSites
      (h_small := smallEtalePullback_fiber_initiallySmall baseMap
        (AlgebraicClosure k) (𝟙 (Spec (.of (AlgebraicClosure k)))))
      (smallEtalePullback baseMap) AddCommGrpCat.{u}).hom.app directImage ≫
    point.sheafFiber.map
      ((HigherDirectImage.baseChange X.hom projection sourceMap baseMap
        (pullback.condition ..) j).app F) ≫
    ((geometricHigherDirectImageFiberIso X j).app
      ((etaleAbelianSheafPullback sourceMap).obj F)).hom

/- Private implementation visibility justification: the computation rule names the private
endpoint transport used by the concrete comparison, without adding a public implementation API. -/
set_option backward.privateInPublic true in
/-- The geometric-stalk comparison is the specified composite of point-comap transport,
ordinary base change, and the derived-sections cohomology identification. -/
theorem higherDirectImageStalkComparison_spec :
    higherDirectImageStalkComparison X F j =
      let baseMap := FieldExtension.specMap k (AlgebraicClosure k)
      let projection := FieldExtension.toBase k (AlgebraicClosure k) X.hom
      let sourceMap := FieldExtension.toSource k (AlgebraicClosure k) X.hom
      let geometricPoint := GeometricPoint.of (AlgebraicClosure k)
        (𝟙 (Spec (.of (AlgebraicClosure k))))
      let point := GeometricPoint.toSmallEtalePoint geometricPoint
      let directImage := Sheaf.higherDirectImage (smallEtalePullback X.hom) F j
      let imagePointTransport := eqToIso (congrArg
        (fun hom : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) ↦
          (Scheme.pointSmallEtale hom).sheafFiber.obj directImage) (Category.id_comp baseMap))
      imagePointTransport.inv ≫
        (GrothendieckTopology.Point.Hom.sheafFiber (A := AddCommGrpCat.{u})
          ⟨smallEtaleInverseImage_comapFiberInv baseMap geometricPoint⟩).app directImage ≫
        (point.sheafFiberComapIsoOfMorphismOfSites
          (h_small := smallEtalePullback_fiber_initiallySmall baseMap
            (AlgebraicClosure k) (𝟙 (Spec (.of (AlgebraicClosure k)))))
          (smallEtalePullback baseMap) AddCommGrpCat.{u}).hom.app directImage ≫
        point.sheafFiber.map
          ((HigherDirectImage.baseChange X.hom projection sourceMap baseMap
            (pullback.condition ..) j).app F) ≫
        ((geometricHigherDirectImageFiberIso X j).app
          ((etaleAbelianSheafPullback sourceMap).obj F)).hom := sorry

/-- The canonical geometric-stalk comparison is an isomorphism of Galois actions. -/
@[stacks 03ST]
theorem higherDirectImageStalk_isog_geometricEtaleCohomology
    [Finite k] [QuasiCompact X.hom] [QuasiSeparated X.hom] :
    ∃ comparison : higherDirectImageStalkGaloisModule X F j ≅
        geometricEtaleCohomologyGaloisModule X F j,
      comparison.hom.hom = higherDirectImageStalkComparison X F j :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
