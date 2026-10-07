module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap70.Lemma_70_19_1_IsoOverOpen

/-!
# Base change of morphisms that are isomorphisms over an open

Slice base change along `f : V ⟶ W` is implemented by the sheaf fibre
product `pullbackOver`, so the functor-of-points data stay those of
`Limits.pullback` rather than the sorry-tainted `HasPullbacks` instance
on `AlgebraicSpace S`. The induced functor on `IsoOverOpen` is the
`ObjectProperty.lift` of this slice functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fibre product `X ×_W V` of an object `g : X ⟶ W` of `Over W` along
`f : V ⟶ W`. -/
def overPullbackObj {S : Scheme.{u}} {V W : AlgebraicSpace S} (f : V ⟶ W)
    (g : Over W) : AlgebraicSpace S :=
  pullbackOver g.hom f W.isSheaf W.representableDiagonal

/-- The first projection `X ×_W V ⟶ X`. -/
def overPullbackFst {S : Scheme.{u}} {V W : AlgebraicSpace S} (f : V ⟶ W)
    (g : Over W) : overPullbackObj f g ⟶ g.left :=
  pullbackOverFst g.hom f W.isSheaf W.representableDiagonal

/-- The second projection `X ×_W V ⟶ V`, the structure morphism of the
base-changed object over `V`. -/
def overPullbackSnd {S : Scheme.{u}} {V W : AlgebraicSpace S} (f : V ⟶ W)
    (g : Over W) : overPullbackObj f g ⟶ V :=
  pullbackOverSnd g.hom f W.isSheaf W.representableDiagonal

/-- The pair `(overPullbackFst f g ≫ u.left, overPullbackSnd f g)` is a cone
over `h.hom` and `f`. -/
theorem overPullback_fst_comp {S : Scheme.{u}} {V W : AlgebraicSpace S}
    (f : V ⟶ W) {g h : Over W} (u : g ⟶ h) :
    (overPullbackFst f g ≫ u.left) ≫ h.hom = overPullbackSnd f g ≫ f :=
  sorry

/-- The morphism `X ×_W V ⟶ X' ×_W V` induced by a morphism of objects of
`Over W`. -/
def overPullbackMap {S : Scheme.{u}} {V W : AlgebraicSpace S} (f : V ⟶ W)
    {g h : Over W} (u : g ⟶ h) :
    overPullbackObj f g ⟶ overPullbackObj f h :=
  pullbackLift h.hom f (overPullbackFst f g ≫ u.left) (overPullbackSnd f g)
    (overPullback_fst_comp f u)

/-- The induced map of fibre products commutes with the projections to `V`. -/
theorem overPullbackMap_snd {S : Scheme.{u}} {V W : AlgebraicSpace S}
    (f : V ⟶ W) {g h : Over W} (u : g ⟶ h) :
    overPullbackMap f u ≫ overPullbackSnd f h = overPullbackSnd f g :=
  sorry

/-- Slice base change along `f : V ⟶ W`, sending `g : X ⟶ W` to
`X ×_W V ⟶ V`. -/
def overPullback {S : Scheme.{u}} {V W : AlgebraicSpace S} (f : V ⟶ W) :
    Over W ⥤ Over V where
  obj g := Over.mk (overPullbackSnd f g)
  map u := Over.homMk (overPullbackMap f u) (overPullbackMap_snd f u)
  map_id := sorry
  map_comp := sorry

/-- The structure morphism of `overPullback f` is the second projection of the
fibre product. -/
theorem overPullback_obj_hom {S : Scheme.{u}} {V W : AlgebraicSpace S}
    (f : V ⟶ W) (g : Over W) :
    ((overPullback f).obj g).hom = overPullbackSnd f g :=
  sorry

namespace IsoOverOpen

/-- Being an isomorphism over an open is stable under base change along any
morphism of algebraic spaces. -/
theorem baseChange_mem {S : Scheme.{u}} {V W U : AlgebraicSpace S}
    (f : V ⟶ W) (ι : U ⟶ W) [IsOpenImmersion ι] (X : IsoOverOpen ι) :
    isoOverOpenProperty (openInverseImageι f ι) ((overPullback f).obj X.obj) :=
  sorry

/-- Base change along `f : V ⟶ W` as a functor on iso-over-open slice
categories. The target open is the inverse image `f⁻¹U`. -/
def baseChange {S : Scheme.{u}} {V W U : AlgebraicSpace S}
    (f : V ⟶ W) (ι : U ⟶ W) [IsOpenImmersion ι] :
    IsoOverOpen ι ⥤ IsoOverOpen (openInverseImageι f ι) :=
  ObjectProperty.lift
    (isoOverOpenProperty (openInverseImageι f ι))
    (inclusion ι ⋙ overPullback f)
    (fun X ↦ baseChange_mem f ι X)

/-- After inclusion into the slice, `baseChange` is ordinary slice base change. -/
def baseChangeInclusionIso {S : Scheme.{u}} {V W U : AlgebraicSpace S}
    (f : V ⟶ W) (ι : U ⟶ W) [IsOpenImmersion ι] :
    baseChange f ι ⋙ inclusion (openInverseImageι f ι) ≅
      inclusion ι ⋙ overPullback f :=
  (isoOverOpenProperty (openInverseImageι f ι)).liftCompιIso
    (inclusion ι ⋙ overPullback f)
    (fun X ↦ baseChange_mem f ι X)

/-- The structure morphism of a `baseChange` object is the second projection
of the fibre product. -/
theorem baseChange_obj_hom {S : Scheme.{u}} {V W U : AlgebraicSpace S}
    (f : V ⟶ W) (ι : U ⟶ W) [IsOpenImmersion ι] (X : IsoOverOpen ι) :
    ((baseChange f ι).obj X).obj.hom = overPullbackSnd f X.obj :=
  sorry

end IsoOverOpen

end AlgebraicGeometry.AlgebraicSpace
