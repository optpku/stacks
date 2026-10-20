module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.MorphismProperty

/-!
# Stability of restricted groupoid schemes

This module records stability of local finite type, local finite presentation, and flatness
for the source and target maps of a restricted groupoid scheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.U)

/-- A morphism property stable under composition and base change descends to the source
map of a restricted groupoid scheme. -/
private lemma restrictedSource_ofStableUnderBaseChange
    {P : CategoryTheory.MorphismProperty Scheme.{u}} [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] (hs : P G.s.left) (hg : P g.left) :
    P (G.pullback g).s.left := by
  let Q : CategoryTheory.MorphismProperty (Over S) := P.inverseImage (Over.forget S)
  have hsPullback : P (Limits.pullback.snd G.s g).left := by
    rw [← Over.forget_map, ← CategoryTheory.Limits.PreservesPullback.iso_hom_snd]
    exact (P.cancel_left_of_respectsIso
      (Limits.PreservesPullback.iso (Over.forget S) G.s g).hom
      (Limits.pullback.snd ((Over.forget S).map G.s) ((Over.forget S).map g))).mpr
        (P.pullback_snd G.s.left g.left hs)
  have hgPullback : P (Limits.pullback.snd g G.t).left := by
    rw [← Over.forget_map, ← CategoryTheory.Limits.PreservesPullback.iso_hom_snd]
    exact (P.cancel_left_of_respectsIso
      (Limits.PreservesPullback.iso (Over.forget S) g G.t).hom
      (Limits.pullback.snd ((Over.forget S).map g) ((Over.forget S).map G.t))).mpr
        (P.pullback_snd g.left G.t.left hg)
  have hOuter : P
      (Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t)).left := by
    rw [← Over.forget_map, ← CategoryTheory.Limits.PreservesPullback.iso_hom_fst]
    exact (P.cancel_left_of_respectsIso
      (Limits.PreservesPullback.iso (Over.forget S) (Limits.pullback.fst G.s g)
        (Limits.pullback.snd g G.t)).hom
      (Limits.pullback.fst ((Over.forget S).map (Limits.pullback.fst G.s g))
        ((Over.forget S).map (Limits.pullback.snd g G.t)))).mpr
        (P.pullback_fst (Limits.pullback.fst G.s g).left (Limits.pullback.snd g G.t).left
          hgPullback)
  have hComposite :
      Q
        ((pullbackArrowIso G g).hom ≫
          Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.snd G.s g) := by
    have hProjected :
        Q
          (Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
            Limits.pullback.snd G.s g) := by
      exact Q.comp_mem _ _ hOuter hsPullback
    exact (Q.cancel_left_of_respectsIso (pullbackArrowIso G g).hom
      (Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.snd G.s g)).mpr hProjected
  have hCompositeLeft : P
      (((pullbackArrowIso G g).hom ≫
          Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.snd G.s g).left) := by
    simpa [Q, MorphismProperty.inverseImage] using hComposite
  have hSource :
      (((pullbackArrowIso G g).hom ≫
          Limits.pullback.fst (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.snd G.s g).left) = (G.pullback g).s.left := by
    simpa [AlgebraicGeometry.GroupoidScheme.pullback] using
      congrArg Over.Hom.left (pullbackArrowIso_hom_upper_snd G g)
  rw [hSource] at hCompositeLeft
  exact hCompositeLeft

/-- A morphism property stable under composition and base change descends to the target
map of a restricted groupoid scheme. -/
private lemma restrictedTarget_ofStableUnderBaseChange
    {P : CategoryTheory.MorphismProperty Scheme.{u}} [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] (ht : P G.t.left) (hg : P g.left) :
    P (G.pullback g).t.left := by
  let Q : CategoryTheory.MorphismProperty (Over S) := P.inverseImage (Over.forget S)
  have hgPullback : P (Limits.pullback.fst g G.t).left := by
    rw [← Over.forget_map, ← CategoryTheory.Limits.PreservesPullback.iso_hom_fst]
    exact (P.cancel_left_of_respectsIso
      (Limits.PreservesPullback.iso (Over.forget S) g G.t).hom
      (Limits.pullback.fst ((Over.forget S).map g) ((Over.forget S).map G.t))).mpr
        (P.pullback_fst g.left G.t.left ht)
  have hUpper : P (Limits.pullback.fst G.s g).left := by
    rw [← Over.forget_map, ← CategoryTheory.Limits.PreservesPullback.iso_hom_fst]
    exact (P.cancel_left_of_respectsIso
      (Limits.PreservesPullback.iso (Over.forget S) G.s g).hom
      (Limits.pullback.fst ((Over.forget S).map G.s) ((Over.forget S).map g))).mpr
        (P.pullback_fst G.s.left g.left hg)
  have hOuter : P
      (Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t)).left := by
    rw [← Over.forget_map, ← CategoryTheory.Limits.PreservesPullback.iso_hom_snd]
    exact (P.cancel_left_of_respectsIso
      (Limits.PreservesPullback.iso (Over.forget S) (Limits.pullback.fst G.s g)
        (Limits.pullback.snd g G.t)).hom
      (Limits.pullback.snd ((Over.forget S).map (Limits.pullback.fst G.s g))
        ((Over.forget S).map (Limits.pullback.snd g G.t)))).mpr
        (P.pullback_snd (Limits.pullback.fst G.s g).left (Limits.pullback.snd g G.t).left
          hUpper)
  have hComposite :
      Q
        ((pullbackArrowIso G g).hom ≫
          Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.fst g G.t) := by
    have hProjected :
        Q
          (Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
            Limits.pullback.fst g G.t) := by
      exact Q.comp_mem _ _ hOuter hgPullback
    exact (Q.cancel_left_of_respectsIso (pullbackArrowIso G g).hom
      (Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
        Limits.pullback.fst g G.t)).mpr hProjected
  have hCompositeLeft : P
      (((pullbackArrowIso G g).hom ≫
          Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.fst g G.t).left) := by
    simpa [Q, MorphismProperty.inverseImage] using hComposite
  have hTarget :
      (((pullbackArrowIso G g).hom ≫
          Limits.pullback.snd (Limits.pullback.fst G.s g) (Limits.pullback.snd g G.t) ≫
          Limits.pullback.fst g G.t).left) = (G.pullback g).t.left := by
    simpa [AlgebraicGeometry.GroupoidScheme.pullback] using
      congrArg Over.Hom.left (pullbackArrowIso_hom_lower_fst G g)
  rw [hTarget] at hCompositeLeft
  exact hCompositeLeft

/-- Restricting a groupoid along a locally finite-type morphism preserves local finite
type of its source map. -/
instance instPullbackSourceLocallyOfFiniteType [LocallyOfFiniteType G.s.left]
    [LocallyOfFiniteType g.left] : LocallyOfFiniteType (G.pullback g).s.left := by
  exact restrictedSource_ofStableUnderBaseChange (G := G) (g := g) inferInstance inferInstance

/-- Restricting a groupoid along a locally finite-type morphism preserves local finite
type of its target map. -/
instance instPullbackTargetLocallyOfFiniteType [LocallyOfFiniteType G.t.left]
    [LocallyOfFiniteType g.left] : LocallyOfFiniteType (G.pullback g).t.left := by
  exact restrictedTarget_ofStableUnderBaseChange (G := G) (g := g) inferInstance inferInstance

/-- Restricting a groupoid along a locally finitely presented morphism preserves local finite
presentation of its source map. -/
instance instPullbackSourceLocallyOfFinitePresentation
    [LocallyOfFinitePresentation G.s.left] [LocallyOfFinitePresentation g.left] :
    LocallyOfFinitePresentation (G.pullback g).s.left := by
  exact restrictedSource_ofStableUnderBaseChange (G := G) (g := g) inferInstance inferInstance

/-- Restricting a groupoid along a locally finitely presented morphism preserves local finite
presentation of its target map. -/
instance instPullbackTargetLocallyOfFinitePresentation
    [LocallyOfFinitePresentation G.t.left] [LocallyOfFinitePresentation g.left] :
    LocallyOfFinitePresentation (G.pullback g).t.left := by
  exact restrictedTarget_ofStableUnderBaseChange (G := G) (g := g) inferInstance inferInstance

/-- Restricting a groupoid along a flat morphism preserves flatness of its source map. -/
instance instPullbackSourceFlat [Flat G.s.left] [Flat g.left] :
    Flat (G.pullback g).s.left := by
  exact restrictedSource_ofStableUnderBaseChange (G := G) (g := g) inferInstance inferInstance

/-- Restricting a groupoid along a flat morphism preserves flatness of its target map. -/
instance instPullbackTargetFlat [Flat G.t.left] [Flat g.left] :
    Flat (G.pullback g).t.left := by
  exact restrictedTarget_ofStableUnderBaseChange (G := G) (g := g) inferInstance inferInstance

/-- If the source map, target map, and restriction morphism are locally of finite type,
then both structure maps of the restricted groupoid are locally of finite type. -/
theorem restrictionLocallyOfFiniteType [LocallyOfFiniteType G.s.left]
    [LocallyOfFiniteType G.t.left] [LocallyOfFiniteType g.left] :
    LocallyOfFiniteType (G.pullback g).s.left ∧
      LocallyOfFiniteType (G.pullback g).t.left :=
  ⟨inferInstance, inferInstance⟩

/-- If the source map, target map, and restriction morphism are locally of finite presentation,
then both structure maps of the restricted groupoid are locally of finite presentation. -/
theorem restrictionLocallyOfFinitePresentation
    [LocallyOfFinitePresentation G.s.left]
    [LocallyOfFinitePresentation G.t.left] [LocallyOfFinitePresentation g.left] :
    LocallyOfFinitePresentation (G.pullback g).s.left ∧
      LocallyOfFinitePresentation (G.pullback g).t.left :=
  ⟨inferInstance, inferInstance⟩

/-- If the source map, target map, and restriction morphism are flat, then both structure
maps of the restricted groupoid are flat. -/
theorem restrictionFlat [Flat G.s.left] [Flat G.t.left] [Flat g.left] :
    Flat (G.pullback g).s.left ∧ Flat (G.pullback g).t.left :=
  ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.GroupoidScheme
