/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Representable.PullbackDiagonal

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import stacks_project.Chap66.Definition_66_18_9_FMap
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap66.Lemma_66_18_3

/-!
# Pullback of modules on algebraic spaces

A morphism of algebraic spaces induces a morphism of small étale ringed topoi. The associated
module inverse image preserves quasi-coherence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Functor-of-points pullbacks exist in the presheaf category on schemes over `S`. -/
instance : HasPullbacks ((Over S)ᵒᵖ ⥤ Type u) := inferInstance

/-- A morphism of algebraic spaces, viewed as a natural transformation of functors of points. -/
def homFunctor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    X.functorOfPoints ⟶ Y.functorOfPoints :=
  f

/-- The functor of points of the fibre product of `X` with a scheme étale over `Y`. -/
def etaleBaseChangeFunctorOfPoints {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) : (Over S)ᵒᵖ ⥤ Type u :=
  pullback (homFunctor f) (homFunctor V.hom)

/-- The algebraic space `X ×_Y V` obtained by pulling back a scheme étale over `Y`. -/
abbrev etaleBaseChangeAtlasScheme {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) : Over S :=
  (Functor.relativelyRepresentable.of_diag Y.representableDiagonal (homFunctor V.hom)).pullback
    (X.atlas.choose_spec.choose ≫ homFunctor f)

set_option backward.isDefEq.respectTransparency false in
/-- Pull the stored source atlas back along the represented target chart. -/
def etaleBaseChangeAtlasMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    yoneda.obj (etaleBaseChangeAtlasScheme f V) ⟶ etaleBaseChangeFunctorOfPoints f V := by
  let p : yoneda.obj X.atlas.choose ⟶ X.functorOfPoints := X.atlas.choose_spec.choose
  let r := Functor.relativelyRepresentable.of_diag Y.representableDiagonal (homFunctor V.hom)
  change yoneda.obj (r.pullback (p ≫ homFunctor f)) ⟶ etaleBaseChangeFunctorOfPoints f V
  exact (IsPullback.of_hasPullback (homFunctor f) (homFunctor V.hom)).flip.lift
    (r.fst (p ≫ homFunctor f)) (yoneda.map (r.snd (p ≫ homFunctor f)) ≫ p)
    ((r.w (p ≫ homFunctor f)).trans (Category.assoc _ _ _).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The atlas square is the actual base change of the source atlas. -/
theorem etaleBaseChangeAtlas_isPullback {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) :
    let p := X.atlas.choose_spec.choose
    let r := Functor.relativelyRepresentable.of_diag Y.representableDiagonal (homFunctor V.hom)
    IsPullback (etaleBaseChangeAtlasMap f V) (yoneda.map (r.snd (p ≫ homFunctor f)))
      (Limits.pullback.fst (homFunctor f) (homFunctor V.hom)) p := by
  dsimp only [etaleBaseChangeAtlasMap]
  exact IsPullback.of_right'
    ((Functor.relativelyRepresentable.of_diag Y.representableDiagonal (homFunctor V.hom)).isPullback
      (X.atlas.choose_spec.choose ≫ homFunctor f))
    (IsPullback.of_hasPullback (homFunctor f) (homFunctor V.hom)).flip

/-- The specified atlas map is representably étale by base change of the input atlas. -/
theorem etaleBaseChangeAtlas_etale {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (etaleBaseChangeAtlasMap f V) := by
  -- Local instance justification (proof-local temporary data): apply relative base-change stability to the atlas pullback square in this proof.
  letI := MorphismProperty.relative_isStableUnderBaseChange
    (F := yoneda) (MorphismProperty.over (X := S)
      (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}))
  exact MorphismProperty.of_isPullback (etaleBaseChangeAtlas_isPullback f V).flip
    X.atlas.choose_spec.choose_spec.1

/-- The specified atlas map is locally surjective by base change of the input atlas. -/
theorem etaleBaseChangeAtlas_surjective {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (etaleBaseChangeAtlasMap f V) := sorry

/-- The fiber product carries the explicitly pulled-back atlas and represented diagonal. -/
def etaleBaseChangeSpace {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    AlgebraicSpace S :=
  ofFunctor (etaleBaseChangeFunctorOfPoints f V) sorry
    (CategoryTheory.Functor.relativelyRepresentable.PullbackDiagonal.diagonal (homFunctor f) (homFunctor V.hom)
      X.representableDiagonal (ofOver_representableDiagonal V.left) Y.representableDiagonal)
    ⟨etaleBaseChangeAtlasScheme f V, etaleBaseChangeAtlasMap f V,
      etaleBaseChangeAtlas_etale f V, etaleBaseChangeAtlas_surjective f V⟩

/-- The first projection of the functor-of-points fibre product. -/
def etaleBaseChangeFst {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    etaleBaseChangeFunctorOfPoints f V ⟶ X.functorOfPoints :=
  pullback.fst (homFunctor f) (homFunctor V.hom)

/-- The second projection of the functor-of-points fibre product. -/
def etaleBaseChangeSndNat {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    etaleBaseChangeFunctorOfPoints f V ⟶ (ofOver V.left).functorOfPoints :=
  pullback.snd (homFunctor f) (homFunctor V.hom)

/-- The projection `X ×_Y V ⟶ X`. -/
def etaleBaseChangeHom {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    etaleBaseChangeSpace f V ⟶ X :=
  etaleBaseChangeFst f V

/-- The projection `X ×_Y V ⟶ V`. -/
def etaleBaseChangeSnd {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    etaleBaseChangeSpace f V ⟶ ofOver V.left :=
  etaleBaseChangeSndNat f V

/-- Base change of an étale morphism of a scheme along a morphism of algebraic spaces is étale. -/
instance etaleBaseChangeHom_isEtale {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) : Etale (etaleBaseChangeHom f V) :=
  sorry

/-- `X ×_Y V` as an object of the étale site of algebraic spaces over `X`. -/
def etaleBaseChangeObj {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    spacesEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (etaleBaseChangeHom f V) inferInstance

/-- The functor-of-points map `X ×_Y V' ⟶ X ×_Y V` induced by a morphism `V' ⟶ V`. -/
def etaleBaseChangeMapNat {X Y : AlgebraicSpace S} (f : X ⟶ Y) {V V' : smallEtaleSite Y}
    (h : V' ⟶ V) :
    etaleBaseChangeFunctorOfPoints f V' ⟶ etaleBaseChangeFunctorOfPoints f V :=
  pullback.map (homFunctor f) (homFunctor V'.hom) (homFunctor f) (homFunctor V.hom)
    (𝟙 X.functorOfPoints) (homFunctor (ofOverMap h.left)) (𝟙 Y.functorOfPoints) sorry sorry

/-- A morphism of schemes étale over `Y` induces a morphism of fibre products over `X`. -/
def etaleBaseChangeMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) {V V' : smallEtaleSite Y}
    (h : V' ⟶ V) : etaleBaseChangeObj f V' ⟶ etaleBaseChangeObj f V :=
  MorphismProperty.Over.homMk (etaleBaseChangeMapNat f h) sorry

/-- Functoriality of `X ×_Y V` in the scheme étale over `Y`. -/
def etaleBaseChange {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    smallEtaleSite Y ⥤ spacesEtaleSite X where
  obj := etaleBaseChangeObj f
  map h := etaleBaseChangeMap f h
  map_id := sorry
  map_comp := sorry

/-- The object map of `etaleBaseChange f` is the fibre product `X ×_Y V`. -/
theorem etaleBaseChange_obj {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    (etaleBaseChange f).obj V = etaleBaseChangeObj f V :=
  rfl

/-- Pullback of étale objects along `f` is continuous for the small étale topology of `Y` and the
spaces étale topology of `X`. -/
instance etaleBaseChange_isContinuous {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (etaleBaseChange f).IsContinuous (smallEtaleTopology Y) (spacesEtaleTopology X) :=
  sorry

/-- The small étale inclusion is continuous, as required to present the extension of sheaves as
a morphism of topoi. -/
instance smallEtaleInclusion_isContinuous (X : AlgebraicSpace S) :
    (smallEtaleInclusion X).IsContinuous (smallEtaleTopology X) (spacesEtaleTopology X) :=
  sorry

/-- Ring-valued sheaves on the small étale site of an algebraic space compose with the forgetful
functor to types. -/
instance smallEtaleTopology_hasSheafCompose_forget_ringCat (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- Ring-valued sheaves on the étale site of algebraic spaces over `X` compose with the forgetful
functor to types. -/
instance spacesEtaleTopology_hasSheafCompose_forget_ringCat (X : AlgebraicSpace S) :
    (spacesEtaleTopology X).HasSheafCompose (forget RingCat.{u}) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
