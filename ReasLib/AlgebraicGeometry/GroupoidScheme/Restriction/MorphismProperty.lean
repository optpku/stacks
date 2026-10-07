module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Comparison
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty

/-!
# Morphism properties of restricted groupoid schemes

This module shows that a morphism property stable under base change passes from the
slicing source map to both structure maps of a restricted groupoid scheme.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A base-change-stable morphism property of the slicing source map holds for the source
map of the restricted groupoid scheme. -/
theorem pullback_source_mem {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hP : P ((pullback.snd g G.t ≫ G.s).left)) : P ((G.pullback g).s.left) := by
  let h : Limits.pullback g G.t ⟶ G.U := pullback.snd g G.t ≫ G.s
  let e :
      (G.toPreRelation.pullback g).left ≅ Limits.pullback h g :=
    pullbackArrowIso G g ≪≫
      pullbackSymmetry (pullback.fst G.s g) (pullback.snd g G.t) ≪≫
        pullbackRightPullbackFstIso G.s g (pullback.snd g G.t)
  -- Base change the sliced source morphism along `g`.
  have hBase : P ((pullback.snd h g).left) := by
    rw [← Over.forget_map, ← CategoryTheory.Limits.PreservesPullback.iso_hom_snd]
    exact (P.cancel_left_of_respectsIso
      (Limits.PreservesPullback.iso (Over.forget S) h g).hom
      (pullback.snd ((Over.forget S).map h) ((Over.forget S).map g))).mpr
        (P.pullback_snd h.left g.left hP)
  -- Transport that base-changed morphism back to the iterated pullback presentation.
  have hSource : P ((e.hom ≫ pullback.snd h g).left) := by
    exact (P.cancel_left_of_respectsIso e.hom.left
      (pullback.snd h g).left).mpr hBase
  -- Read the transported morphism as the restricted source map.
  have hRewrite : (e.hom ≫ pullback.snd h g).left = (G.pullback g).s.left := by
    simpa [e, h, AlgebraicGeometry.GroupoidScheme.pullback, Category.assoc] using
      congrArg Over.Hom.left (pullbackArrowIso_hom_upper_snd G g)
  rwa [hRewrite] at hSource

/-- A base-change-stable morphism property of the slicing source map holds for the target
map of the restricted groupoid scheme. -/
theorem pullback_target_mem {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hP : P ((pullback.snd g G.t ≫ G.s).left)) : P ((G.pullback g).t.left) := by
  let H := G.pullback g
  -- In the point groupoid of `H`, applying inversion twice to the identity arrow is trivial.
  have hii : H.i ≫ H.i = 𝟙 H.R := by
    -- Local instance justification (proof-local temporary data): the explicit point-groupoid instance is confined to this involution proof.
    letI := H.pointGroupoid H.R
    let f : H.s ⟶ H.t :=
      ⟨𝟙 H.R, by simp, by simp⟩
    have hInvInv : CategoryTheory.Groupoid.inv (CategoryTheory.Groupoid.inv f) = f := by
      simp [f]
    have hArrow :
        (CategoryTheory.Groupoid.inv (CategoryTheory.Groupoid.inv f)).arrow = f.arrow := by
      exact congrArg (fun p => p.arrow) hInvInv
    change ((f.arrow ≫ H.i) ≫ H.i = f.arrow) at hArrow
    simpa [f, Category.assoc] using hArrow
  have hiiLeft : H.i.left ≫ H.i.left = 𝟙 H.R.left := by
    simpa using congrArg Over.Hom.left hii
  -- Package the involution as an automorphism of the restricted arrow scheme.
  let iLeftIso : H.R.left ≅ H.R.left :=
    { hom := H.i.left
      inv := H.i.left
      hom_inv_id := hiiLeft
      inv_hom_id := hiiLeft }
  let e : Arrow.mk H.s.left ≅ Arrow.mk H.t.left :=
    Arrow.isoMk iLeftIso (Iso.refl _) (congrArg Over.Hom.left H.inverse_target)
  -- Transport the already established source-side property across that arrow isomorphism.
  exact (P.arrow_mk_iso_iff e).mp (pullback_source_mem G g P hP)

/-- If the slicing source map of a restricted groupoid scheme has a morphism property
stable under base change, then both restricted structure maps have that property. -/
theorem pullback_source_target_mem {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hP : P ((pullback.snd g G.t ≫ G.s).left)) :
    P ((G.pullback g).s.left) ∧ P ((G.pullback g).t.left) :=
  ⟨pullback_source_mem G g P hP, pullback_target_mem G g P hP⟩

/-- If the slicing source map of a second restriction has a base-change-stable,
target-local morphism property, and the first slicing source map covers its open image,
then the slicing source map of the composite restriction has the property. -/
theorem property_compRestriction_of_restriction {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U')
    (τ : DescentTopology) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget τ.precoverage]
    (V : Scheme.Opens G.U.left) (hToImage : (Limits.pullback g G.t).left ⟶ V.toScheme)
    (h_range : Set.range (pullback.snd g G.t ≫ G.s).left.base =
      (V : Set G.U.left))
    (h_factor : hToImage ≫ V.ι = (pullback.snd g G.t ≫ G.s).left)
    (h_cover : Presieve.singleton hToImage ∈ τ.precoverage V.toScheme)
    (hP : P (pullback.snd g' (G.pullback g).t ≫ (G.pullback g).s).left) :
    P (pullback.snd (g' ≫ g) G.t ≫ G.s).left := sorry

/-- If the original target map is a cover and the slicing source map of a composite
restriction has a base-change-stable, target-local morphism property, then the slicing
source map of the second restriction has the property. -/
theorem property_restriction_of_compRestriction {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U')
    (τ : DescentTopology) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget τ.precoverage]
    (h_cover : Presieve.singleton G.t.left ∈ τ.precoverage G.U.left)
    (hP : P (pullback.snd (g' ≫ g) G.t ≫ G.s).left) :
    P (pullback.snd g' (G.pullback g).t ≫ (G.pullback g).s).left := sorry

end AlgebraicGeometry.GroupoidScheme
