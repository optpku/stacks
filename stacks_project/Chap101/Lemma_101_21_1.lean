module

public import Mathlib.RingTheory.Regular.RegularSequence
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap76.Lemma_76_28_1_Germ
public import stacks_project.Chap76.Lemma_76_28_1_Vanishing
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap100.Lemma_100_4_1_FieldValuedPoint
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Slicing a flat locally finitely presented morphism to an algebraic stack

A regular sequence in the étale local ring of a field-valued fibre of a flat,
locally finitely presented morphism from an algebraic space to an algebraic
stack cuts out a closed subspace that remains flat and locally of finite
presentation over the stack after shrinking the source around the image of the
fibre point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The projection `F ⟶ U` of a cartesian field fibre, recovered from an
algebraic-space model of `TwoFibreProduct.apex f p.hom`. -/
def representedFiberι {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} {f : U.toGroupoids ⟶ X} {p : FieldValuedPoint X}
    {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids) :
    F ⟶ U :=
  AlgebraicSpace.toGroupoids.eval
    (e.inv ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f p.hom)

/-- `representedFiberι e` is the morphism of algebraic spaces recovered from
`e.inv ≫ TwoFibreProduct.fst f p.hom`. -/
theorem representedFiberι_eq {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} {f : U.toGroupoids ⟶ X} {p : FieldValuedPoint X}
    {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids) :
    representedFiberι e =
      AlgebraicSpace.toGroupoids.eval
        (e.inv ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f p.hom) :=
  sorry

/-- The structure morphism `V(fs) ∩ W ⟶ X` obtained by composing the inclusion
of the open subspace with `f : U.toGroupoids ⟶ X`. -/
def vanishingToStack {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} (f : U.toGroupoids ⟶ X) {r : ℕ}
    (fs : Fin r → AlgebraicSpace.globalSectionsRing U)
    (W : AlgebraicSpace.OpenSubspace U) :
    (AlgebraicSpace.vanishingPullback fs W).toGroupoids ⟶ X :=
  AlgebraicSpace.toGroupoids.map
      (AlgebraicSpace.vanishingPullbackι fs W ≫ W.ι) ≫
    f

/-- `vanishingToStack f fs W` is `toGroupoids.map (vanishingPullbackι fs W ≫ W.ι) ≫ f`. -/
theorem vanishingToStack_eq {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} (f : U.toGroupoids ⟶ X) {r : ℕ}
    (fs : Fin r → AlgebraicSpace.globalSectionsRing U)
    (W : AlgebraicSpace.OpenSubspace U) :
    vanishingToStack f fs W =
      AlgebraicSpace.toGroupoids.map
          (AlgebraicSpace.vanishingPullbackι fs W ≫ W.ι) ≫
        f :=
  sorry

/-- The germ `Γ(U, 𝒪_U) →+* 𝒪_{F, zbar}` along `representedFiberι e`, formed in an
étale neighbourhood of the image of `zbar` on `U`. -/
def globalSectionsToRepresentedFiberEtaleLocalRingAt {S : Scheme.{u}}
    {U : AlgebraicSpace S} {X : GroupoidsOver S} {f : U.toGroupoids ⟶ X}
    {p : FieldValuedPoint X} {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids)
    (zbar : AlgebraicSpace.GeometricPoint F)
    (V : AlgebraicSpace.smallEtaleSite U)
    (l : (toSmallEtalePoint (zbar.map (representedFiberι e))).fiber.obj V) :
    AlgebraicSpace.globalSectionsRing U →+* AlgebraicSpace.etaleLocalRing F zbar :=
  ((AlgebraicSpace.etaleLocalRingMap (representedFiberι e) zbar).comp
      (AlgebraicSpace.globalSectionsToEtaleLocalRing U
        (zbar.map (representedFiberι e)))).comp
    (RingCat.Hom.hom
      ((toSmallEtalePoint (zbar.map (representedFiberι e))).toPresheafFiber V l
        (AlgebraicSpace.globalSectionsConstPresheaf U)))

/-- `globalSectionsToRepresentedFiberEtaleLocalRingAt` composes the local ring
map of `representedFiberι e` with the germ of global sections at the image of
`zbar` on `U`. -/
theorem globalSectionsToRepresentedFiberEtaleLocalRingAt_eq {S : Scheme.{u}}
    {U : AlgebraicSpace S} {X : GroupoidsOver S} {f : U.toGroupoids ⟶ X}
    {p : FieldValuedPoint X} {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids)
    (zbar : AlgebraicSpace.GeometricPoint F)
    (V : AlgebraicSpace.smallEtaleSite U)
    (l : (toSmallEtalePoint (zbar.map (representedFiberι e))).fiber.obj V) :
    globalSectionsToRepresentedFiberEtaleLocalRingAt e zbar V l =
      ((AlgebraicSpace.etaleLocalRingMap (representedFiberι e) zbar).comp
          (AlgebraicSpace.globalSectionsToEtaleLocalRing U
            (zbar.map (representedFiberι e)))).comp
        (RingCat.Hom.hom
          ((toSmallEtalePoint (zbar.map (representedFiberι e))).toPresheafFiber V l
            (AlgebraicSpace.globalSectionsConstPresheaf U))) :=
  sorry

/-- Lemma 101.21.1: Let `X` be an algebraic stack over a scheme `S`. Let
`f : U.toGroupoids ⟶ X` be a morphism from an algebraic space which is flat and
locally of finite presentation, and let `p` be a field-valued point of `X`.
Let `fs` be a finite family of global sections of `𝒪_U`, let `F` be an
algebraic-space model of the cartesian field fibre `U ×_X Spec(k)` via an
equivalence `e` with `TwoFibreProduct.apex f p.hom`, and let `z` be a point of
`F` with geometric point `zbar` lying over `z`, such that the images of `fs`
form a regular sequence in `𝒪_{F, zbar}`. Then after replacing `U` by an open
subspace containing the image of `z` in `|U|`, the morphism
`V(fs) ⟶ X` is flat and locally of finite presentation. -/
@[stacks 06MD]
theorem exists_openSubspace_vanishing_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] (f : U.toGroupoids ⟶ X)
    [Flat f] [LocallyOfFinitePresentation f] (p : FieldValuedPoint X) {r : ℕ}
    (fs : Fin r → AlgebraicSpace.globalSectionsRing U) {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids)
    (z : AlgebraicSpace.Points F) (zbar : AlgebraicSpace.GeometricPoint F)
    (hz : zbar.liesOver z)
    (hreg : ∀ (V : AlgebraicSpace.smallEtaleSite U)
        (l : (toSmallEtalePoint (zbar.map (representedFiberι e))).fiber.obj V),
      RingTheory.Sequence.IsRegular (AlgebraicSpace.etaleLocalRing F zbar)
        (List.ofFn fun i ↦
          globalSectionsToRepresentedFiberEtaleLocalRingAt e zbar V l (fs i))) :
    ∃ W : AlgebraicSpace.OpenSubspace U,
      AlgebraicSpace.Points.map (representedFiberι e) z ∈ W.pointsSet ∧
        Flat (vanishingToStack f fs W) ∧
          LocallyOfFinitePresentation (vanishingToStack f fs W) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
