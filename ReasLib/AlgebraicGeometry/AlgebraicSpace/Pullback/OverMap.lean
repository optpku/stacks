module

public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Base change of a morphism of algebraic spaces over a common target

A morphism `c : X ⟶ Y` over `T` induces, after base change along `φ : Z ⟶ T`,
a morphism `overMap c hc φ : X ×_T Z ⟶ Y ×_T Z`. Specialising `φ` to the
spectrum of a residue field or to an open of a scheme recovers the fibre map
and the restriction of the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open ReasLibPullback

/-- The pair `(pullback.fst f φ ≫ c, pullback.snd f φ)` equalizes `g` and `φ`
when `c` is a morphism over `T`. -/
theorem overMap_condition {S : Scheme.{u}} {X Y T Z : AlgebraicSpace S}
    {f : X ⟶ T} {g : Y ⟶ T} (c : X ⟶ Y) (hc : c ≫ g = f) (φ : Z ⟶ T) :
    (pullback.fst f φ ≫ c) ≫ g = pullback.snd f φ ≫ φ :=
  (Category.assoc (pullback.fst f φ) c g).trans <|
    (congrArg (CategoryStruct.comp (pullback.fst f φ)) hc).trans pullback.condition

/-- The base change of a morphism `c : X ⟶ Y` over `T` along `φ : Z ⟶ T`. -/
def overMap {S : Scheme.{u}} {X Y T Z : AlgebraicSpace S}
    {f : X ⟶ T} {g : Y ⟶ T} (c : X ⟶ Y) (hc : c ≫ g = f) (φ : Z ⟶ T) :
    pullback f φ ⟶ pullback g φ :=
  pullback.lift (pullback.fst f φ ≫ c) (pullback.snd f φ) (overMap_condition c hc φ)

/-- `overMap c hc φ` is the pullback lift of `(pullback.fst f φ ≫ c, pullback.snd f φ)`. -/
theorem overMap_eq {S : Scheme.{u}} {X Y T Z : AlgebraicSpace S}
    {f : X ⟶ T} {g : Y ⟶ T} (c : X ⟶ Y) (hc : c ≫ g = f) (φ : Z ⟶ T) :
    overMap c hc φ =
      pullback.lift (pullback.fst f φ ≫ c) (pullback.snd f φ)
        (overMap_condition c hc φ) :=
  rfl

/-- The first projection of `overMap c hc φ` is `pullback.fst f φ ≫ c`. -/
theorem overMap_fst {S : Scheme.{u}} {X Y T Z : AlgebraicSpace S}
    {f : X ⟶ T} {g : Y ⟶ T} (c : X ⟶ Y) (hc : c ≫ g = f) (φ : Z ⟶ T) :
    overMap c hc φ ≫ pullback.fst g φ = pullback.fst f φ ≫ c :=
  pullback.lift_fst (pullback.fst f φ ≫ c) (pullback.snd f φ) (overMap_condition c hc φ)

/-- The second projection of `overMap c hc φ` is `pullback.snd f φ`. -/
theorem overMap_snd {S : Scheme.{u}} {X Y T Z : AlgebraicSpace S}
    {f : X ⟶ T} {g : Y ⟶ T} (c : X ⟶ Y) (hc : c ≫ g = f) (φ : Z ⟶ T) :
    overMap c hc φ ≫ pullback.snd g φ = pullback.snd f φ :=
  pullback.lift_snd (pullback.fst f φ ≫ c) (pullback.snd f φ) (overMap_condition c hc φ)

/-- The open immersion of an open of `S` as a morphism of algebraic spaces over `S`. -/
def openι {S : Scheme.{u}} (U : S.Opens) :
    ofOver (Over.mk U.ι) ⟶ ofOver (Over.mk (𝟙 S)) :=
  ofOverHomMk U.ι (Category.comp_id U.ι)

/-- `openι U` is `ofOverHomMk` of the open immersion `U.ι`. -/
theorem openι_eq {S : Scheme.{u}} (U : S.Opens) :
    openι U = ofOverHomMk U.ι (Category.comp_id U.ι) :=
  rfl

/-- The fibre of a morphism over `S` at a point `s`, as the base change of `c`
along `Spec κ(s) ⟶ S`. -/
def fiberMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ ofOver (Over.mk (𝟙 S))} {g : Y ⟶ ofOver (Over.mk (𝟙 S))}
    (c : X ⟶ Y) (hc : c ≫ g = f) (s : S) :
    pullback f (ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _)) ⟶
      pullback g (ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _)) :=
  overMap c hc (ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _))

/-- `fiberMap c hc s` is `overMap` along `ofOverHomMk` of `S.fromSpecResidueField s`. -/
theorem fiberMap_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ ofOver (Over.mk (𝟙 S))} {g : Y ⟶ ofOver (Over.mk (𝟙 S))}
    (c : X ⟶ Y) (hc : c ≫ g = f) (s : S) :
    fiberMap c hc s =
      overMap c hc (ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _)) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
