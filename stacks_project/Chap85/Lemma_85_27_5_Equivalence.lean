/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_27_2_Datum
public import stacks_project.Chap85.Lemma_85_27_4

/-!
# Equivalence between cartesian schemes over a Čech nerve and descent data

The construction of Lemma 85.27.4 extends to an equivalence of categories between
cartesian simplicial schemes over `f.simplicialScheme` and descent data relative to
`f : X ⟶ S`. The inverse reconstructs a cartesian pair via the Čech identifications
of degrees `0` and `1`, then applies `CartesianDatum.ofDatum`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial
open CategoryTheory.SimplicialObject CategoryTheory.Arrow

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.DescentData

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The morphism of descent data induced by a morphism of cartesian schemes over the
Čech nerve of `f`, using the degree-zero component over `X`. -/
def ofCartesianOverMap {Y Z : CartesianOver f.simplicialScheme} (φ : Y ⟶ Z) :
    ofCartesianOver f Y ⟶ ofCartesianOver f Z where
  hom _ := Over.homMk (φ.hom.left.app (op ⦋0⦌)) sorry
  comm := sorry

/-- The functor sending a cartesian simplicial scheme over `f.simplicialScheme` to the
associated descent datum relative to `f`. -/
def ofCartesianOverFunctor :
    CartesianOver f.simplicialScheme ⥤
      DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f) where
  obj Y := ofCartesianOver f Y
  map φ := ofCartesianOverMap f φ
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- On objects, `ofCartesianOverFunctor f` is `ofCartesianOver f`. -/
theorem ofCartesianOverFunctor_obj (Y : CartesianOver f.simplicialScheme) :
    (ofCartesianOverFunctor f).obj Y = ofCartesianOver f Y := sorry

/-- The scheme over `(X/S)_0` obtained by transporting the unique component of a descent
datum along the degree-zero Čech identification `(X/S)_0 ≅ X`. -/
def toCartesianDatumSchemeOver
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :
    Over (f.simplicialScheme.obj (op ⦋0⦌)) :=
  (Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj (D.obj default)

/-- Čech identification of the `δ 1` face pullback of a scheme over `X` with the
`pullback.fst` pullback, after transporting bases along the degree-zero and degree-one
Čech identifications. -/
def overPullbackFaceOneIso (V : Over X) :
    (Over.pullback (f.simplicialScheme.δ (1 : Fin 2))).obj
        ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V) ≅
      (Over.map (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv).obj
        ((Over.pullback (pullback.fst f f)).obj V) :=
  Over.isoMk
    { hom :=
        pullback.map
          (((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V).hom)
          (f.simplicialScheme.δ (1 : Fin 2)) V.hom (pullback.fst f f) (𝟙 _)
          (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).hom
          (cechNerve.degreeZero.iso (Arrow.mk f)).hom sorry sorry
      inv :=
        pullback.map V.hom (pullback.fst f f)
          (((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V).hom)
          (f.simplicialScheme.δ (1 : Fin 2)) (𝟙 _)
          (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv
          (cechNerve.degreeZero.iso (Arrow.mk f)).inv sorry sorry
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

/-- Čech identification of the `δ 0` face pullback of a scheme over `X` with the
`pullback.snd` pullback, after transporting bases along the degree-zero and degree-one
Čech identifications. -/
def overPullbackFaceZeroIso (V : Over X) :
    (Over.pullback (f.simplicialScheme.δ (0 : Fin 2))).obj
        ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V) ≅
      (Over.map (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv).obj
        ((Over.pullback (pullback.snd f f)).obj V) :=
  Over.isoMk
    { hom :=
        pullback.map
          (((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V).hom)
          (f.simplicialScheme.δ (0 : Fin 2)) V.hom (pullback.snd f f) (𝟙 _)
          (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).hom
          (cechNerve.degreeZero.iso (Arrow.mk f)).hom sorry sorry
      inv :=
        pullback.map V.hom (pullback.snd f f)
          (((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).obj V).hom)
          (f.simplicialScheme.δ (0 : Fin 2)) (𝟙 _)
          (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv
          (cechNerve.degreeZero.iso (Arrow.mk f)).inv sorry sorry
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

/-- The face-pullback isomorphism of a descent datum, transported to an isomorphism over
`(X/S)_1` between the `δ 1` and `δ 0` pullbacks. -/
def toCartesianDatumIso
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :
    (Over.pullback (f.simplicialScheme.δ (1 : Fin 2))).obj
        (toCartesianDatumSchemeOver f D) ≅
      (Over.pullback (f.simplicialScheme.δ (0 : Fin 2))).obj
        (toCartesianDatumSchemeOver f D) :=
  overPullbackFaceOneIso f (D.obj default) ≪≫
    (Over.map (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv).mapIso
      (CategoryTheory.Pseudofunctor.DescentData.iso D (pullback.fst f f ≫ f)
        (pullback.fst f f) (pullback.snd f f) sorry sorry) ≪≫
    (overPullbackFaceZeroIso f (D.obj default)).symm

/-- The functor sending descent data relative to `f` to the corresponding cartesian pair
over `f.simplicialScheme`, by transporting along the Čech identifications of degrees `0`
and `1`. -/
def toCartesianDatum :
    DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f) ⥤
      CartesianDatum f.simplicialScheme where
  obj D :=
    CartesianDatum.ofPullbackIso (toCartesianDatumSchemeOver f D)
      (toCartesianDatumIso f D) sorry sorry
  map {D E} φ :=
    CartesianDatum.homMk
      ((Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).inv).map (φ.hom default)) sorry
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- The underlying scheme over `(X/S)_0` of `toCartesianDatum f` is the unique descent
component transported along the degree-zero Čech identification. -/
theorem toCartesianDatum_schemeOver
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :
    ((toCartesianDatum f).obj D).schemeOver =
      Over.mk ((D.obj default).hom ≫ (cechNerve.degreeZero.iso (Arrow.mk f)).inv) :=
  sorry

/-- The quasi-inverse of `ofCartesianOverFunctor f`, reconstructing a cartesian simplicial
scheme from a descent datum via `CartesianDatum.ofDatum`. -/
def ofCartesianOverInverse :
    DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f) ⥤
      CartesianOver f.simplicialScheme :=
  toCartesianDatum f ⋙ CartesianDatum.ofDatum

/-- Comparison of cartesian pairs extracted from a cartesian scheme over the Čech nerve
directly, versus after passing through descent data and transporting along
`(X/S)_0 ≅ X`. -/
def toCartesianDatumCompare (Y : CartesianOver f.simplicialScheme) :
    CartesianDatum.toDatum.obj Y ≅
      (toCartesianDatum f).obj ((ofCartesianOverFunctor f).obj Y) where
  hom := CartesianDatum.homMk (Over.homMk (𝟙 _) sorry) sorry
  inv := CartesianDatum.homMk (Over.homMk (𝟙 _) sorry) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The unit isomorphism of the cartesian-over / descent-data equivalence, at an object
`Y`. -/
def ofCartesianOverUnitApp (Y : CartesianOver f.simplicialScheme) :
    Y ≅ (ofCartesianOverInverse f).obj ((ofCartesianOverFunctor f).obj Y) :=
  CartesianDatum.unitApp Y ≪≫
    CartesianDatum.ofDatum.mapIso (toCartesianDatumCompare f Y)

/-- The unit natural isomorphism `𝟭 ≅ ofCartesianOverFunctor f ⋙ ofCartesianOverInverse f`. -/
def ofCartesianOverUnitIso :
    𝟭 (CartesianOver f.simplicialScheme) ≅
      ofCartesianOverFunctor f ⋙ ofCartesianOverInverse f :=
  NatIso.ofComponents (fun Y ↦ ofCartesianOverUnitApp f Y) sorry

/-- Degree-zero comparison over `X` between the reconstructed descent component and the
original unique component of `D`, obtained by transporting `CartesianDatum.counitSchemeOverIso`
along the degree-zero Čech identification. -/
def ofCartesianOverCounitOverIso
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :
    ((ofCartesianOverFunctor f).obj ((ofCartesianOverInverse f).obj D)).obj default ≅
      D.obj default :=
  (Over.map (cechNerve.degreeZero.iso (Arrow.mk f)).hom).mapIso
      (CartesianDatum.counitSchemeOverIso ((toCartesianDatum f).obj D)) ≪≫
    (Over.mapIso (cechNerve.degreeZero.iso (Arrow.mk f))).counitIso.app (D.obj default)

/-- The counit isomorphism of the cartesian-over / descent-data equivalence, at a descent
datum `D`. -/
def ofCartesianOverCounitApp
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :
    (ofCartesianOverInverse f ⋙ ofCartesianOverFunctor f).obj D ≅ D :=
  CategoryTheory.Pseudofunctor.DescentData.isoMk
    (fun (_ : PUnit.{v + 1}) ↦ ofCartesianOverCounitOverIso.{u, v, u + 1} f D) sorry

/-- The counit natural isomorphism
`ofCartesianOverInverse f ⋙ ofCartesianOverFunctor f ≅ 𝟭`. -/
def ofCartesianOverCounitIso :
    ofCartesianOverInverse f ⋙ ofCartesianOverFunctor f ≅
      𝟭 (DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f)) :=
  NatIso.ofComponents (fun D ↦ ofCartesianOverCounitApp f D) sorry

end AlgebraicGeometry.Scheme.DescentData
