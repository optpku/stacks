/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.Sites.Limits
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap97.Lemma_97_10_1_Sheaf

/-!
# Base change of relative Hom

The identification `Mor_{B'}(Z', X') ≅ B' ×_B Mor_B(Z, X)` of fppf sheaves on
`Sch/S`, for the chosen fibre products `Z' = B' ×_B Z` and `X' = B' ×_B X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {B B' : AlgebraicSpace S}

/-- The chosen fibre product `Y' = B' ×_B Y`, viewed as an object over `B'`. -/
abbrev pullbackObj (Y : Over B) (h : B' ⟶ B) : Over B' :=
  Over.mk (pullback.fst h Y.hom)

/-- The structure morphism of `pullbackObj Y h` is the projection `B' ×_B Y ⟶ B'`. -/
theorem pullbackObj_hom (Y : Over B) (h : B' ⟶ B) :
    (pullbackObj Y h).hom = pullback.fst h Y.hom :=
  sorry

/-- The canonical isomorphism `T ×_{B'} Y' ≅ T ×_B Y` obtained by pasting the
fibre-product square of `Y' = B' ×_B Y`. -/
def fiberIso (Y : Over B) (h : B' ⟶ B) {T : Over S} (a' : ofOver T ⟶ B') :
    pullback a' (pullbackObj Y h).hom ≅ pullback (a' ≫ h) Y.hom :=
  pullbackRightPullbackFstIso h Y.hom a'

/-- `fiberIso` identifies the projections to `T`. -/
theorem fiberIso_fst (Y : Over B) (h : B' ⟶ B) {T : Over S} (a' : ofOver T ⟶ B') :
    (fiberIso Y h a').hom ≫ pullback.fst (a' ≫ h) Y.hom =
      pullback.fst a' (pullbackObj Y h).hom :=
  sorry

/-- `fiberIso` identifies the projections to `Y`. -/
theorem fiberIso_snd (Y : Over B) (h : B' ⟶ B) {T : Over S} (a' : ofOver T ⟶ B') :
    (fiberIso Y h a').hom ≫ pullback.snd (a' ≫ h) Y.hom =
      pullback.snd a' (pullbackObj Y h).hom ≫ pullback.snd h Y.hom :=
  sorry

/-- The forward functor-of-points map, sending a pair over `B'` to the pair over
`B` with base `a' ≫ h` and morphism transported along `fiberIso`. -/
def pairMap (Z X : Over B) (h : B' ⟶ B) {T : Over S}
    (p : HomPair (pullbackObj Z h) (pullbackObj X h) T) : HomPair Z X T :=
  HomPair.ofOverMorph (p.base ≫ h)
    ((fiberIso Z h p.base).inv ≫ HomPair.toOverMorph p ≫ pullback.snd h X.hom) sorry

/-- The inverse functor-of-points map, reconstructing a pair over `B'` from a
`B'`-point and a compatible relative-Hom pair over `B`. -/
def pairInv (Z X : Over B) (h : B' ⟶ B) {T : Over S} (a' : ofOver T ⟶ B')
    (q : HomPair Z X T) (hq : a' ≫ h = q.base) :
    HomPair (pullbackObj Z h) (pullbackObj X h) T :=
  HomPair.ofOverMorph a'
    (pullback.lift (pullback.fst a' (pullbackObj Z h).hom ≫ a')
      ((fiberIso Z h a').hom ≫
        eqToHom (congrArg (fun t ↦ pullback t Z.hom) hq) ≫ HomPair.toOverMorph q)
      sorry)
    sorry

/-- Equality of `Mor_{B'}(Z', X')` and `B' ×_B Mor_B(Z, X)` as functors of
points, recorded as an equivalence on pairs. -/
def pairEquiv (Z X : Over B) (h : B' ⟶ B) (T : Over S) :
    HomPair (pullbackObj Z h) (pullbackObj X h) T ≃
      { p : (ofOver T ⟶ B') × HomPair Z X T // p.1 ≫ h = p.2.base } where
  toFun p := ⟨⟨p.base, pairMap Z X h p⟩, rfl⟩
  invFun p := pairInv Z X h p.1.1 p.1.2 p.2
  left_inv := sorry
  right_inv := sorry

/-- `pairEquiv` sends a pair to its `B'`-point together with `pairMap`. -/
theorem pairEquiv_apply (Z X : Over B) (h : B' ⟶ B) {T : Over S}
    (p : HomPair (pullbackObj Z h) (pullbackObj X h) T) :
    (pairEquiv Z X h T p).1 = ⟨p.base, pairMap Z X h p⟩ :=
  sorry

/-- The inverse of `pairEquiv` is `pairInv` on a compatible pair of points. -/
theorem pairEquiv_symm_apply (Z X : Over B) (h : B' ⟶ B) {T : Over S}
    (p : (ofOver T ⟶ B') × HomPair Z X T) (hp : p.1 ≫ h = p.2.base) :
    (pairEquiv Z X h T).symm ⟨p, hp⟩ = pairInv Z X h p.1 p.2 hp :=
  sorry

/-- The sheaf morphism `Mor_{B'}(Z', X') ⟶ Mor_B(Z, X)` induced by `pairMap`. -/
def toHomSheaf (Z X : Over B) (h : B' ⟶ B) :
    homSheaf (pullbackObj Z h) (pullbackObj X h) ⟶ homSheaf Z X :=
  Sheaf.homEquiv.symm
    { app T := TypeCat.ofHom (pairMap Z X h)
      naturality := sorry }

/-- Components of `toHomSheaf` are `pairMap`. -/
theorem toHomSheaf_app (Z X : Over B) (h : B' ⟶ B) (T : (Over S)ᵒᵖ)
    (p : HomPair (pullbackObj Z h) (pullbackObj X h) T.unop) :
    (toHomSheaf Z X h).hom.app T p = pairMap Z X h p :=
  sorry

/-- The inverse sheaf morphism of `pullbackIso`, reconstructed objectwise by
`pairInv` from the projections of the chosen sheaf fibre product. -/
def pullbackIso_inv (Z X : Over B) (h : B' ⟶ B) :
    pullback (uliftSheafMap h) (toBase Z X) ⟶
      homSheaf (pullbackObj Z h) (pullbackObj X h) :=
  Sheaf.homEquiv.symm
    { app T :=
        TypeCat.ofHom fun x ↦
          pairInv Z X h
            (yonedaEquiv.symm
              ((pullback.fst (uliftSheafMap h) (toBase Z X)).hom.app T x).down)
            ((pullback.snd (uliftSheafMap h) (toBase Z X)).hom.app T x) sorry
      naturality := sorry }

/-- The canonical isomorphism `Mor_{B'}(Z', X') ≅ B' ×_B Mor_B(Z, X)` of fppf
sheaves on `Sch/S`. -/
def pullbackIso (Z X : Over B) (h : B' ⟶ B) :
    homSheaf (pullbackObj Z h) (pullbackObj X h) ≅
      pullback (uliftSheafMap h) (toBase Z X) where
  hom :=
    pullback.lift (toBase (pullbackObj Z h) (pullbackObj X h))
      (toHomSheaf Z X h) sorry
  inv := pullbackIso_inv Z X h
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The first projection of `pullbackIso.hom` is the structure map of
`Mor_{B'}(Z', X')`. -/
theorem pullbackIso_hom_fst (Z X : Over B) (h : B' ⟶ B) :
    (pullbackIso Z X h).hom ≫ pullback.fst (uliftSheafMap h) (toBase Z X) =
      toBase (pullbackObj Z h) (pullbackObj X h) :=
  sorry

/-- The second projection of `pullbackIso.hom` is `toHomSheaf`. -/
theorem pullbackIso_hom_snd (Z X : Over B) (h : B' ⟶ B) :
    (pullbackIso Z X h).hom ≫ pullback.snd (uliftSheafMap h) (toBase Z X) =
      toHomSheaf Z X h :=
  sorry

/-- The square relating `Mor_{B'}(Z', X')` to `Mor_B(Z, X)` over `B' ⟶ B` is
cartesian in fppf sheaves on `Sch/S`. -/
theorem isPullback (Z X : Over B) (h : B' ⟶ B) :
    IsPullback (toBase (pullbackObj Z h) (pullbackObj X h)) (toHomSheaf Z X h)
      (uliftSheafMap h) (toBase Z X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
