/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback

/-!
# Topology of groupoid schemes

This module records topological properties of the composition morphism of a groupoid scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- If the object scheme of a groupoid scheme is the spectrum of a field, then its composition
morphism is universally open. -/
theorem universallyOpen_c {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) : UniversallyOpen G.c.left := by
  have htToSpec : UniversallyOpen (G.t.left ≫ eU.inv) := by
    let X : Over (Spec (CommRingCat.of k)) := Over.mk (G.t.left ≫ eU.inv)
    simpa [X] using inferInstanceAs (UniversallyOpen X.hom)
  have ht : UniversallyOpen G.t.left := by
    simpa using MorphismProperty.RespectsIso.postcomp
      (@UniversallyOpen) eU.hom (G.t.left ≫ eU.inv) htToSpec
  let e :
      (pullback G.s G.t).left ≅ pullback G.t.left G.t.left :=
    (Over.forget S).mapIso G.targetComparisonIso.symm ≪≫
      PreservesPullback.iso (Over.forget S) G.t G.t
  have hcOver :
      ((Over.forget S).mapIso G.targetComparisonIso.symm).hom ≫
          (pullback.snd G.t G.t).left = G.c.left := by
    simpa [targetComparisonIso_inv] using
      congrArg Over.Hom.left (targetComparisonInv_snd G)
  have hc :
      e.hom ≫ pullback.snd G.t.left G.t.left = G.c.left := by
    change ((Over.forget S).mapIso G.targetComparisonIso.symm).hom ≫
        (PreservesPullback.iso (Over.forget S) G.t G.t).hom ≫
        pullback.snd G.t.left G.t.left = G.c.left
    calc
      Over.Hom.left G.targetComparisonIso.inv ≫
          pullbackComparison (Over.forget S) G.t G.t ≫ pullback.snd G.t.left G.t.left =
        Over.Hom.left G.targetComparisonIso.inv ≫ Over.Hom.left (pullback.snd G.t G.t) := by
          simpa using congrArg (fun f ↦ Over.Hom.left G.targetComparisonIso.inv ≫ f)
            (PreservesPullback.iso_hom_snd (Over.forget S) G.t G.t)
      _ = G.c.left := by
        simpa [targetComparisonIso_inv] using hcOver
  rw [← hc]
  exact MorphismProperty.RespectsIso.precomp
    (@UniversallyOpen) e.hom (pullback.snd G.t.left G.t.left)
    (inferInstanceAs (UniversallyOpen (pullback.snd G.t.left G.t.left)))

/-- If the object scheme of a groupoid scheme is the spectrum of a field, then its composition
morphism is an open map. -/
theorem isOpenMap_c {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) : IsOpenMap G.c.left :=
  @Scheme.Hom.isOpenMap _ _ G.c.left (universallyOpen_c G eU)

end AlgebraicGeometry.GroupoidScheme
