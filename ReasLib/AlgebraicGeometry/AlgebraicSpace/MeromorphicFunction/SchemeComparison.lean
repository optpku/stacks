module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import ReasLib.Topology.Sheaves.Pullback.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.WeaklyAssociatedPoints

/-!
# Associated étale meromorphic-function algebras

If `T` is a scheme over `S`, the Zariski sheaf of meromorphic functions on `T.left` determines an
étale sheaf of rings on `ofOver T` by, on each étale object `U`, taking global sections of the
Zariski sheafification of the pushout presheaf
`W ↦ 𝒪_U(W) ⊗_{(f⁻¹𝒪)(W)} (f⁻¹𝒦_{T.left})(W)` along `f = associatedSchemeHom T U`, then applying
the universe lift `CommRingCat.{u} ⥤ CommRingCat.{u+1}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme morphism from an étale object `U` over `ofOver T` to the representing scheme
`T.left`. -/
def associatedSchemeHom {S : Scheme.{u}} (T : Over S) (U : smallEtaleSite (ofOver T)) :
    U.left.left ⟶ T.left :=
  (Yoneda.fullyFaithful.preimage (U.hom : yoneda.obj U.left ⟶ yoneda.obj T)).left

/-- `associatedSchemeHom T U` is the underlying scheme morphism of the Yoneda preimage of
`U.hom`. -/
theorem associatedSchemeHom_eq {S : Scheme.{u}} (T : Over S) (U : smallEtaleSite (ofOver T)) :
    associatedSchemeHom T U =
      (Yoneda.fullyFaithful.preimage (U.hom : yoneda.obj U.left ⟶ yoneda.obj T)).left :=
  rfl

/-- Inverse image of a Zariski sheaf of commutative rings on `T.left` along
`associatedSchemeHom T U`. -/
def associatedInverseImage {S : Scheme.{u}} (T : Over S) (U : smallEtaleSite (ofOver T))
    (F : TopCat.Sheaf CommRingCat.{u} T.left.toTopCat) :
    TopCat.Sheaf CommRingCat.{u} U.left.left.toTopCat :=
  (TopCat.Sheaf.pullback CommRingCat.{u} (associatedSchemeHom T U).base).obj F

/-- `associatedInverseImage T U F` is topological sheaf pullback of `F` along
`associatedSchemeHom T U`. -/
theorem associatedInverseImage_eq {S : Scheme.{u}} (T : Over S) (U : smallEtaleSite (ofOver T))
    (F : TopCat.Sheaf CommRingCat.{u} T.left.toTopCat) :
    associatedInverseImage T U F =
      (TopCat.Sheaf.pullback CommRingCat.{u} (associatedSchemeHom T U).base).obj F :=
  rfl

/-- The underlying continuous maps of a triangle `U ⟶ V ⟶ T.left` agree. -/
theorem associatedSchemeHom_base_comp {S : Scheme.{u}} (T : Over S)
    {U V : smallEtaleSite (ofOver T)} (φ : U ⟶ V) :
    φ.left.left.base ≫ (associatedSchemeHom T V).base = (associatedSchemeHom T U).base :=
  congrArg (fun f : U.left.left ⟶ T.left ↦ f.base)
    (congrArg Over.Hom.left
      ((Yoneda.fullyFaithful.preimage_comp ((ofOverFunctor S).map φ.left) V.hom).symm.trans
        (congrArg Yoneda.fullyFaithful.preimage φ.w)))

/-- Restriction of inverse-image sections along a morphism in the small étale site, evaluated on a
Zariski open of the target. -/
def associatedInverseImageMap {S : Scheme.{u}} (T : Over S)
    {U V : smallEtaleSite (ofOver T)} (φ : U ⟶ V)
    (F : TopCat.Sheaf CommRingCat.{u} T.left.toTopCat)
    (W : Opens V.left.left.toTopCat) :
    (associatedInverseImage T V F).obj.obj (op W) ⟶
      (associatedInverseImage T U F).obj.obj (op ((Opens.map φ.left.left.base).obj W)) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} φ.left.left.base).unit.app
      (associatedInverseImage T V F)).hom.app (op W) ≫
    ((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u})
        φ.left.left.base (associatedSchemeHom T V).base).hom.app F).hom.app
      (op ((Opens.map φ.left.left.base).obj W)) ≫
    ((TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
        (associatedSchemeHom_base_comp T φ)).hom.app F).hom.app
      (op ((Opens.map φ.left.left.base).obj W))

/-- `associatedInverseImageMap` is unit, composition, and congruence of inverse images. -/
theorem associatedInverseImageMap_eq {S : Scheme.{u}} (T : Over S)
    {U V : smallEtaleSite (ofOver T)} (φ : U ⟶ V)
    (F : TopCat.Sheaf CommRingCat.{u} T.left.toTopCat)
    (W : Opens V.left.left.toTopCat) :
    associatedInverseImageMap T φ F W =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} φ.left.left.base).unit.app
          (associatedInverseImage T V F)).hom.app (op W) ≫
        ((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u})
            φ.left.left.base (associatedSchemeHom T V).base).hom.app F).hom.app
          (op ((Opens.map φ.left.left.base).obj W)) ≫
        ((TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
            (associatedSchemeHom_base_comp T φ)).hom.app F).hom.app
          (op ((Opens.map φ.left.left.base).obj W)) :=
  rfl

/-- The adjoint structure-sheaf map `f⁻¹ 𝒪_{T.left} ⟶ 𝒪_U` on a Zariski open. -/
def associatedInverseImageStructureHom {S : Scheme.{u}} (T : Over S)
    (U : smallEtaleSite (ofOver T)) (W : Opens U.left.left.toTopCat) :
    (associatedInverseImage T U T.left.sheaf).obj.obj (op W) ⟶
      U.left.left.sheaf.obj.obj (op W) :=
  (RingedSpace.Hom.inverseImageStructureSheafHomComm
      (associatedSchemeHom T U).toLRSHom.toShHom).hom.app (op W)

/-- `associatedInverseImageStructureHom` is the component of the inverse-image adjunction
transpose of `associatedSchemeHom T U`. -/
theorem associatedInverseImageStructureHom_eq {S : Scheme.{u}} (T : Over S)
    (U : smallEtaleSite (ofOver T)) (W : Opens U.left.left.toTopCat) :
    associatedInverseImageStructureHom T U W =
      (RingedSpace.Hom.inverseImageStructureSheafHomComm
          (associatedSchemeHom T U).toLRSHom.toShHom).hom.app (op W) :=
  rfl

/-- The inverse image of `𝒪_{T.left} ⟶ 𝒦_{T.left}` on a Zariski open. -/
def associatedInverseImageMeromorphicHom {S : Scheme.{u}} (T : Over S)
    (U : smallEtaleSite (ofOver T)) (W : Opens U.left.left.toTopCat) :
    (associatedInverseImage T U T.left.sheaf).obj.obj (op W) ⟶
      (associatedInverseImage T U
        T.left.toLocallyRingedSpace.meromorphicFunctionSheaf).obj.obj (op W) :=
  ((TopCat.Sheaf.pullback CommRingCat.{u} (associatedSchemeHom T U).base).map
      T.left.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).hom.app (op W)

/-- `associatedInverseImageMeromorphicHom` is the component of the inverse image of
`toMeromorphicFunctionSheafHom` on `T.left`. -/
theorem associatedInverseImageMeromorphicHom_eq {S : Scheme.{u}} (T : Over S)
    (U : smallEtaleSite (ofOver T)) (W : Opens U.left.left.toTopCat) :
    associatedInverseImageMeromorphicHom T U W =
      ((TopCat.Sheaf.pullback CommRingCat.{u} (associatedSchemeHom T U).base).map
          T.left.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).hom.app (op W) :=
  rfl

/-- The Zariski pushout presheaf `W ↦ 𝒪_U(W) ⊗_{(f⁻¹𝒪)(W)} (f⁻¹𝒦_{T.left})(W)`. -/
def associatedMeromorphicFunctionZariskiPresheaf {S : Scheme.{u}} (T : Over S)
    (U : smallEtaleSite (ofOver T)) :
    (Opens U.left.left.toTopCat)ᵒᵖ ⥤ CommRingCat.{u} where
  obj W :=
    pushout (associatedInverseImageStructureHom T U W.unop)
      (associatedInverseImageMeromorphicHom T U W.unop)
  map f :=
    pushout.map (associatedInverseImageStructureHom T U _)
      (associatedInverseImageMeromorphicHom T U _)
      (associatedInverseImageStructureHom T U _)
      (associatedInverseImageMeromorphicHom T U _)
      (U.left.left.sheaf.obj.map f)
      ((associatedInverseImage T U
          T.left.toLocallyRingedSpace.meromorphicFunctionSheaf).obj.map f)
      ((associatedInverseImage T U T.left.sheaf).obj.map f) sorry sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- `associatedMeromorphicFunctionZariskiPresheaf` is the objectwise pushout of inverse-image
sections. -/
theorem associatedMeromorphicFunctionZariskiPresheaf_obj {S : Scheme.{u}} (T : Over S)
    (U : smallEtaleSite (ofOver T)) (W : Opens U.left.left.toTopCat) :
    (associatedMeromorphicFunctionZariskiPresheaf T U).obj (op W) =
      pushout (associatedInverseImageStructureHom T U W)
        (associatedInverseImageMeromorphicHom T U W) :=
  rfl

/-- The Zariski sheafification of the associated meromorphic-algebra pushout presheaf on
`U.left.left`. -/
def associatedMeromorphicFunctionZariskiSheaf {S : Scheme.{u}} (T : Over S)
    (U : smallEtaleSite (ofOver T)) :
    TopCat.Sheaf CommRingCat.{u} U.left.left.toTopCat :=
  (presheafToSheaf (Opens.grothendieckTopology U.left.left.toTopCat) CommRingCat.{u}).obj
    (associatedMeromorphicFunctionZariskiPresheaf T U)

/-- `associatedMeromorphicFunctionZariskiSheaf T U` is `presheafToSheaf` of the pushout
presheaf. -/
theorem associatedMeromorphicFunctionZariskiSheaf_eq {S : Scheme.{u}} (T : Over S)
    (U : smallEtaleSite (ofOver T)) :
    associatedMeromorphicFunctionZariskiSheaf T U =
      (presheafToSheaf (Opens.grothendieckTopology U.left.left.toTopCat) CommRingCat.{u}).obj
        (associatedMeromorphicFunctionZariskiPresheaf T U) :=
  rfl

/-- Associated meromorphic algebra on an étale object: global sections of the Zariski
sheafification of `W ↦ 𝒪_U(W) ⊗_{(f⁻¹𝒪)(W)} (f⁻¹𝒦_{T.left})(W)`. -/
def associatedMeromorphicFunctionObj {S : Scheme.{u}} (T : Over S)
    (U : smallEtaleSite (ofOver T)) : CommRingCat.{u} :=
  (associatedMeromorphicFunctionZariskiSheaf T U).obj.obj (op ⊤)

/-- `associatedMeromorphicFunctionObj T U` is evaluation of the sheafified pushout at the top
open. -/
theorem associatedMeromorphicFunctionObj_eq {S : Scheme.{u}} (T : Over S)
    (U : smallEtaleSite (ofOver T)) :
    associatedMeromorphicFunctionObj T U =
      (associatedMeromorphicFunctionZariskiSheaf T U).obj.obj (op ⊤) :=
  rfl

/-- The `𝒪_U`-algebra structure map of `associatedMeromorphicFunctionObj T U`. -/
def associatedMeromorphicFunctionObjStructureHom {S : Scheme.{u}} (T : Over S)
    (U : smallEtaleSite (ofOver T)) :
    (commStructurePresheaf (ofOver T)).obj (op U) ⟶ associatedMeromorphicFunctionObj T U :=
  pushout.inl (associatedInverseImageStructureHom T U ⊤)
    (associatedInverseImageMeromorphicHom T U ⊤) ≫
    (toSheafify (Opens.grothendieckTopology U.left.left.toTopCat)
      (associatedMeromorphicFunctionZariskiPresheaf T U)).app (op ⊤)

/-- `associatedMeromorphicFunctionObjStructureHom` is the sheafified left pushout coprojection
on global sections. -/
theorem associatedMeromorphicFunctionObjStructureHom_eq {S : Scheme.{u}} (T : Over S)
    (U : smallEtaleSite (ofOver T)) :
    associatedMeromorphicFunctionObjStructureHom T U =
      pushout.inl (associatedInverseImageStructureHom T U ⊤)
        (associatedInverseImageMeromorphicHom T U ⊤) ≫
        (toSheafify (Opens.grothendieckTopology U.left.left.toTopCat)
          (associatedMeromorphicFunctionZariskiPresheaf T U)).app (op ⊤) :=
  rfl

/-- Pushforward of associated Zariski pushout presheaves along a morphism in the small étale
site. -/
def associatedMeromorphicFunctionZariskiPresheafPushforwardMap {S : Scheme.{u}} (T : Over S)
    {U V : smallEtaleSite (ofOver T)} (φ : U ⟶ V) :
    associatedMeromorphicFunctionZariskiPresheaf T V ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} φ.left.left.base).obj
        (associatedMeromorphicFunctionZariskiPresheaf T U) where
  app W :=
    pushout.map (associatedInverseImageStructureHom T V W.unop)
      (associatedInverseImageMeromorphicHom T V W.unop)
      (associatedInverseImageStructureHom T U ((Opens.map φ.left.left.base).obj W.unop))
      (associatedInverseImageMeromorphicHom T U ((Opens.map φ.left.left.base).obj W.unop))
      (φ.left.left.app W.unop)
      (associatedInverseImageMap T φ
        T.left.toLocallyRingedSpace.meromorphicFunctionSheaf W.unop)
      (associatedInverseImageMap T φ T.left.sheaf W.unop) sorry sorry
  naturality _ _ _ := sorry

/-- Restriction of associated meromorphic algebras along a morphism in the small étale site. -/
def associatedMeromorphicFunctionObjMap {S : Scheme.{u}} (T : Over S)
    {U V : smallEtaleSite (ofOver T)} (φ : U ⟶ V) :
    associatedMeromorphicFunctionObj T V ⟶ associatedMeromorphicFunctionObj T U :=
  (sheafifyLift (Opens.grothendieckTopology V.left.left.toTopCat)
      (associatedMeromorphicFunctionZariskiPresheafPushforwardMap T φ ≫
        (TopCat.Presheaf.pushforward CommRingCat.{u} φ.left.left.base).map
          (toSheafify (Opens.grothendieckTopology U.left.left.toTopCat)
            (associatedMeromorphicFunctionZariskiPresheaf T U)))
      ((TopCat.Sheaf.pushforward CommRingCat.{u} φ.left.left.base).obj
        (associatedMeromorphicFunctionZariskiSheaf T U)).property).app (op ⊤)

/-- The unlifted étale presheaf of associated meromorphic algebras. -/
def associatedMeromorphicFunctionPresheafUnlifted {S : Scheme.{u}} (T : Over S) :
    (smallEtaleSite (ofOver T))ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := associatedMeromorphicFunctionObj T U.unop
  map f := associatedMeromorphicFunctionObjMap T f.unop
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The unlifted associated meromorphic presheaf evaluates on an étale chart to its
associated meromorphic algebra. -/
theorem associatedMeromorphicFunctionPresheafUnlifted_obj {S : Scheme.{u}} (T : Over S)
    (U : smallEtaleSite (ofOver T)) :
    (associatedMeromorphicFunctionPresheafUnlifted T).obj (op U) =
      associatedMeromorphicFunctionObj T U :=
  rfl

/-- Universe lift of the associated meromorphic-algebra presheaf. -/
def associatedMeromorphicFunctionPresheaf {S : Scheme.{u}} (T : Over S) :
    (smallEtaleSite (ofOver T))ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  associatedMeromorphicFunctionPresheafUnlifted T ⋙ CommRingCat.universeLift.{u, u + 1}

/-- `associatedMeromorphicFunctionPresheaf` is universe lift of the unlifted associated
presheaf. -/
theorem associatedMeromorphicFunctionPresheaf_eq {S : Scheme.{u}} (T : Over S) :
    associatedMeromorphicFunctionPresheaf T =
      associatedMeromorphicFunctionPresheafUnlifted T ⋙
        CommRingCat.universeLift.{u, u + 1} :=
  rfl

/-- The unlifted associated meromorphic-algebra presheaf is a sheaf on the small étale site. -/
theorem associatedMeromorphicFunctionPresheafUnlifted_isSheaf {S : Scheme.{u}} (T : Over S) :
    Presheaf.IsSheaf (smallEtaleTopology (ofOver T))
      (associatedMeromorphicFunctionPresheafUnlifted T) :=
  sorry

/-- The associated meromorphic-algebra presheaf is a sheaf after universe lift. -/
theorem associatedMeromorphicFunctionPresheaf_isSheaf {S : Scheme.{u}} (T : Over S) :
    Presheaf.IsSheaf (smallEtaleTopology (ofOver T))
      (associatedMeromorphicFunctionPresheaf T) :=
  sorry

/-- The étale sheaf of meromorphic functions associated to `𝒦_{T.left}`. -/
def associatedMeromorphicFunctionSheaf {S : Scheme.{u}} (T : Over S) :
    Sheaf (smallEtaleTopology (ofOver T)) CommRingCat.{u + 1} :=
  ⟨associatedMeromorphicFunctionPresheaf T, associatedMeromorphicFunctionPresheaf_isSheaf T⟩

/-- `associatedMeromorphicFunctionSheaf T` is the universe lift of the sheafified objectwise
pushout of `𝒪_U` with the inverse image of `𝒦_{T.left}`. -/
theorem associatedMeromorphicFunctionSheaf_eq {S : Scheme.{u}} (T : Over S) :
    associatedMeromorphicFunctionSheaf T =
      ⟨associatedMeromorphicFunctionPresheaf T, associatedMeromorphicFunctionPresheaf_isSheaf T⟩ :=
  rfl

/-- The canonical `𝒪`-algebra structure map of the associated étale meromorphic-function sheaf. -/
def associatedToMeromorphicFunctionSheafHom {S : Scheme.{u}} (T : Over S) :
    commStructureSheafLift (ofOver T) ⟶ associatedMeromorphicFunctionSheaf T :=
  { hom :=
      { app := fun U ↦
          CommRingCat.universeLift.{u, u + 1}.map
            (associatedMeromorphicFunctionObjStructureHom T U.unop)
        naturality := fun _ _ _ ↦ sorry } }

/-- `associatedToMeromorphicFunctionSheafHom T` is the universe lift of the sheafified pushout
coprojections `𝒪_U ⟶ Γ(U, 𝒪_U ⊗_{f⁻¹𝒪} f⁻¹𝒦)`. -/
theorem associatedToMeromorphicFunctionSheafHom_eq {S : Scheme.{u}} (T : Over S)
    (U : smallEtaleSite (ofOver T)) :
    (associatedToMeromorphicFunctionSheafHom T).hom.app (op U) =
      CommRingCat.universeLift.{u, u + 1}.map
        (associatedMeromorphicFunctionObjStructureHom T U) :=
  rfl

/-- The associated étale meromorphic-function algebra is quasi-coherent as an `𝒪`-module. -/
theorem associatedMeromorphicFunctionSheaf_isQuasicoherent {S : Scheme.{u}} (T : Over S)
    [HasFiniteIrreducibleComponentsOnCompactOpens (ofOver T)]
    (hweak : (ofOver T).weakAss ⊆ codimZeroPoints (ofOver T)) :
    ((restrictionAlong (associatedToMeromorphicFunctionSheafHom T)).obj
        (unitModule (smallEtaleTopology (ofOver T))
          (associatedMeromorphicFunctionSheaf T))).IsQuasicoherent :=
  sorry

/-- If every weakly associated point of the representable algebraic space `ofOver T` has
codimension zero and it has finitely many irreducible components on compact opens, its
meromorphic-function algebra is isomorphic to the étale algebra associated to the Zariski
meromorphic-function sheaf of `T.left`. -/
@[stacks 0EN7]
theorem meromorphicFunctionSheaf_isIsomorphic_associated {S : Scheme.{u}} (T : Over S)
    [HasFiniteIrreducibleComponentsOnCompactOpens (ofOver T)]
    (hweak : (ofOver T).weakAss ⊆ codimZeroPoints (ofOver T)) :
    IsIsomorphic (Under.mk (toMeromorphicFunctionSheafHom (ofOver T)))
      (Under.mk (associatedToMeromorphicFunctionSheafHom T)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
