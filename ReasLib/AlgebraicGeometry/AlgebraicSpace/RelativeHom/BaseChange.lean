module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.SheafHom

/-!
# Base change of relative morphism sheaves

The relative-Hom sheaf is compatible with pullback of the base algebraic space.
-/

public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {B B' : AlgebraicSpace S}

/-- The chosen fibre product `Y' = B' ×_B Y`, viewed as an object over `B'`. -/
abbrev pullbackObj (Y : Over B) (h : B' ⟶ B) : Over B' :=
  Over.mk (pullback.fst h Y.hom)

/-- The structure morphism of `pullbackObj Y h` is the projection to `B'`. -/
theorem pullbackObj_hom (Y : Over B) (h : B' ⟶ B) :
    (pullbackObj Y h).hom = pullback.fst h Y.hom :=
  sorry

/-- The canonical isomorphism `T ×_{B'} Y' ≅ T ×_B Y` obtained by pasting
the fibre-product square defining `Y'`. -/
def fiberIso (Y : Over B) (h : B' ⟶ B) {T : Over S} (a' : ofOver T ⟶ B') :
    pullback a' (pullbackObj Y h).hom ≅ pullback (a' ≫ h) Y.hom :=
  pullbackRightPullbackFstIso h Y.hom a'

/-- `fiberIso` identifies the projections to the test scheme. -/
theorem fiberIso_fst (Y : Over B) (h : B' ⟶ B) {T : Over S} (a' : ofOver T ⟶ B') :
    (fiberIso Y h a').hom ≫ pullback.fst (a' ≫ h) Y.hom =
      pullback.fst a' (pullbackObj Y h).hom :=
  sorry

/-- `fiberIso` identifies the projections to `Y`. -/
theorem fiberIso_snd (Y : Over B) (h : B' ⟶ B) {T : Over S} (a' : ofOver T ⟶ B') :
    (fiberIso Y h a').hom ≫ pullback.snd (a' ≫ h) Y.hom =
      pullback.snd a' (pullbackObj Y h).hom ≫ pullback.snd h Y.hom :=
  sorry

/-- The forward map on relative-morphism pairs induced by base change. -/
def pairMap (Z X : Over B) (h : B' ⟶ B) {T : Over S}
    (p : Pair (pullbackObj Z h).hom (pullbackObj X h).hom T) : Pair Z.hom X.hom T :=
  Pair.mk (p.a ≫ h)
    (BaseChangeMorphism.ofMap
      ((fiberIso Z h p.a).inv ≫ BaseChangeMorphism.toMap p.b ≫ pullback.snd h X.hom)
      sorry)

/-- The inverse map on relative-morphism pairs induced by base change. -/
def pairInv (Z X : Over B) (h : B' ⟶ B) {T : Over S} (a' : ofOver T ⟶ B')
    (q : Pair Z.hom X.hom T) (hq : a' ≫ h = q.a) :
    Pair (pullbackObj Z h).hom (pullbackObj X h).hom T :=
  Pair.mk a'
    (BaseChangeMorphism.ofMap
      (pullback.lift (pullback.fst a' (pullbackObj Z h).hom ≫ a')
        ((fiberIso Z h a').hom ≫
          eqToHom (congrArg (fun t ↦ pullback t Z.hom) hq) ≫
            BaseChangeMorphism.toMap q.b)
        sorry)
      sorry)

/-- The pointwise equivalence between relative morphisms after base change and
compatible pairs consisting of a base point and an original relative morphism. -/
def pairEquiv (Z X : Over B) (h : B' ⟶ B) (T : Over S) :
    Pair (pullbackObj Z h).hom (pullbackObj X h).hom T ≃
      { p : (ofOver T ⟶ B') × Pair Z.hom X.hom T // p.1 ≫ h = p.2.a } where
  toFun p := ⟨⟨p.a, pairMap Z X h p⟩, rfl⟩
  invFun p := pairInv Z X h p.1.1 p.1.2 p.2
  left_inv := sorry
  right_inv := sorry

/-- `pairEquiv` sends a pair to its base point and transported relative morphism. -/
theorem pairEquiv_apply (Z X : Over B) (h : B' ⟶ B) {T : Over S}
    (p : Pair (pullbackObj Z h).hom (pullbackObj X h).hom T) :
    (pairEquiv Z X h T p).1 = ⟨p.a, pairMap Z X h p⟩ :=
  sorry

/-- The inverse of `pairEquiv` is `pairInv` on compatible data. -/
theorem pairEquiv_symm_apply (Z X : Over B) (h : B' ⟶ B) {T : Over S}
    (p : (ofOver T ⟶ B') × Pair Z.hom X.hom T) (hp : p.1 ≫ h = p.2.a) :
    (pairEquiv Z X h T).symm ⟨p, hp⟩ = pairInv Z X h p.1 p.2 hp :=
  sorry

/-- The sheaf morphism induced by transporting relative-morphism pairs. -/
def toHomSheaf (Z X : Over B) (h : B' ⟶ B) :
    sheaf (pullbackObj Z h).hom (pullbackObj X h).hom ⟶ sheaf Z.hom X.hom :=
  Sheaf.homEquiv.symm
    { app T := TypeCat.ofHom (pairMap Z X h)
      naturality := sorry }

/-- The components of `toHomSheaf` are the pointwise transport maps. -/
theorem toHomSheaf_app (Z X : Over B) (h : B' ⟶ B) (T : (Over S)ᵒᵖ)
    (p : Pair (pullbackObj Z h).hom (pullbackObj X h).hom T.unop) :
    (toHomSheaf Z X h).hom.app T p = pairMap Z X h p :=
  sorry

/-- The inverse sheaf morphism reconstructed objectwise from compatible pairs. -/
def pullbackIso_inv (Z X : Over B) (h : B' ⟶ B) :
    pullback (toSheaf.map h) (baseMap Z X) ⟶
      sheaf (pullbackObj Z h).hom (pullbackObj X h).hom :=
  Sheaf.homEquiv.symm
    { app T :=
        TypeCat.ofHom fun x ↦
          pairInv Z X h
            (yonedaEquiv.symm
              ((pullback.fst (toSheaf.map h) (baseMap Z X)).hom.app T x).down)
            ((pullback.snd (toSheaf.map h) (baseMap Z X)).hom.app T x) sorry
      naturality := sorry }

/-- The canonical isomorphism between the base-changed relative-Hom sheaf and
the pullback of the original relative-Hom sheaf. -/
def pullbackIso (Z X : Over B) (h : B' ⟶ B) :
    sheaf (pullbackObj Z h).hom (pullbackObj X h).hom ≅
      pullback (toSheaf.map h) (baseMap Z X) where
  hom :=
    pullback.lift (baseMap (pullbackObj Z h) (pullbackObj X h))
      (toHomSheaf Z X h) sorry
  inv := pullbackIso_inv Z X h
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The first projection of `pullbackIso.hom` is the base projection. -/
theorem pullbackIso_hom_fst (Z X : Over B) (h : B' ⟶ B) :
    (pullbackIso Z X h).hom ≫ pullback.fst (toSheaf.map h) (baseMap Z X) =
      baseMap (pullbackObj Z h) (pullbackObj X h) :=
  sorry

/-- The second projection of `pullbackIso.hom` is `toHomSheaf`. -/
theorem pullbackIso_hom_snd (Z X : Over B) (h : B' ⟶ B) :
    (pullbackIso Z X h).hom ≫ pullback.snd (toSheaf.map h) (baseMap Z X) =
      toHomSheaf Z X h :=
  sorry

/-- The square defined by `pullbackIso` is cartesian in fppf sheaves. -/
theorem isPullback (Z X : Over B) (h : B' ⟶ B) :
    IsPullback (baseMap (pullbackObj Z h) (pullbackObj X h))
      (toHomSheaf Z X h) (toSheaf.map h) (baseMap Z X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
