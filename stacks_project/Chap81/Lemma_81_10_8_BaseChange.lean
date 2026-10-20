/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap81.«81_10_6_1_Glueing»
public import stacks_project.Chap81.«81_10_6_2_Square»

/-!
# Flat base change of formal-glueing categories

A morphism `g : X' ⟶ X` of algebraic spaces induces fibre products
`Z' = Limits.pullback i g` and `Y' = Limits.pullback f g`, together with the
pullback functor `QCoh(Y → X, Z) ⥤ QCoh(Y' → X', Z')` on glueing triples.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QCoh
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing

/-- The chosen fibre product `Z' = Z ×_X X'`, isomorphic to the source fibre product
`X' ×_X Z` by `pullbackSymmetry`. -/
abbrev Z' {S : Scheme.{u}} {X Z X' : AlgebraicSpace S} (i : Z ⟶ X) (g : X' ⟶ X) :
    AlgebraicSpace S :=
  Limits.pullback i g

/-- The chosen fibre product `Y' = Y ×_X X'`, isomorphic to the source fibre product
`X' ×_X Y` by `pullbackSymmetry`. -/
abbrev Y' {S : Scheme.{u}} {X Y X' : AlgebraicSpace S} (f : Y ⟶ X) (g : X' ⟶ X) :
    AlgebraicSpace S :=
  Limits.pullback f g

/-- The base change `i' : Z' ⟶ X'` of a closed immersion `i : Z ⟶ X`. -/
abbrev i' {S : Scheme.{u}} {X Z X' : AlgebraicSpace S} (i : Z ⟶ X) (g : X' ⟶ X) :
    Z' i g ⟶ X' :=
  Limits.pullback.snd i g

/-- The base change `f' : Y' ⟶ X'` of `f : Y ⟶ X`. -/
abbrev f' {S : Scheme.{u}} {X Y X' : AlgebraicSpace S} (f : Y ⟶ X) (g : X' ⟶ X) :
    Y' f g ⟶ X' :=
  Limits.pullback.snd f g

/-- The projection `Z' ⟶ Z` of the chosen fibre product. -/
abbrev toZ {S : Scheme.{u}} {X Z X' : AlgebraicSpace S} (i : Z ⟶ X) (g : X' ⟶ X) :
    Z' i g ⟶ Z :=
  Limits.pullback.fst i g

/-- The projection `Y' ⟶ Y` of the chosen fibre product. -/
abbrev toY {S : Scheme.{u}} {X Y X' : AlgebraicSpace S} (f : Y ⟶ X) (g : X' ⟶ X) :
    Y' f g ⟶ Y :=
  Limits.pullback.fst f g

/-- The base change `i' i g` of a closed immersion remains a closed immersion. -/
instance instIsClosedImmersion_i' {S : Scheme.{u}} {X Z X' : AlgebraicSpace S}
    (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    IsClosedImmersion (i' i g) :=
  IsClosedImmersion.of_isPullback (IsPullback.flip (IsPullback.of_hasPullback i g))

/-- The first projection of `Z' i g` is the map `Z' ⟶ Z`. -/
theorem Z'_fst {S : Scheme.{u}} {X Z X' : AlgebraicSpace S} (i : Z ⟶ X) (g : X' ⟶ X) :
    toZ i g ≫ i = i' i g ≫ g :=
  sorry

/-- The first projection of `Y' f g` is the map `Y' ⟶ Y`. -/
theorem Y'_fst {S : Scheme.{u}} {X Y X' : AlgebraicSpace S} (f : Y ⟶ X) (g : X' ⟶ X) :
    toY f g ≫ f = f' f g ≫ g :=
  sorry

/-- The composite of the complement inclusion of `i' i g` with `g` misses the closed
image of `i`. -/
theorem complementBaseChange_misses {S : Scheme.{u}} {X Z X' : AlgebraicSpace S}
    (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    ∀ (W : (Over S)ᵒᵖ)
      (t : (closedImmersionComplement (i' i g)).functorOfPoints.obj W),
      missesClosedImage i ((closedImmersionComplementι (i' i g) ≫ g).app W t) :=
  sorry

/-- The comparison `U' ⟶ U` of open complements of `i'` and `i`. -/
def complementBaseChange {S : Scheme.{u}} {X Z X' : AlgebraicSpace S}
    (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    closedImmersionComplement (i' i g) ⟶ closedImmersionComplement i where
  app W := TypeCat.ofHom fun t ↦
    ⟨(closedImmersionComplementι (i' i g) ≫ g).app W t,
      complementBaseChange_misses i g W t⟩
  naturality := sorry

/-- The square of complement inclusions over `g` commutes. -/
theorem complementBaseChange_comp {S : Scheme.{u}} {X Z X' : AlgebraicSpace S}
    (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    complementBaseChange i g ≫ closedImmersionComplementι i =
      closedImmersionComplementι (i' i g) ≫ g :=
  sorry

/-- The composite of the complement inclusion of `inverseImageι (f' f g) (i' i g)` with
`toY f g` misses the closed image of `inverseImageι f i`. -/
theorem overlapBaseChange_misses {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    ∀ (W : (Over S)ᵒᵖ)
      (t : (closedImmersionComplement (inverseImageι (f' f g) (i' i g))).functorOfPoints.obj W),
      missesClosedImage (inverseImageι f i)
        ((closedImmersionComplementι (inverseImageι (f' f g) (i' i g)) ≫
            toY f g).app W t) :=
  sorry

/-- The comparison `V' ⟶ V` of closed-immersion complements of the inverse images of
`i'` and `i`. -/
def overlapBaseChange {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    closedImmersionComplement (inverseImageι (f' f g) (i' i g)) ⟶
      closedImmersionComplement (inverseImageι f i) where
  app W := TypeCat.ofHom fun t ↦
    ⟨(closedImmersionComplementι (inverseImageι (f' f g) (i' i g)) ≫ toY f g).app W t,
      overlapBaseChange_misses f i g W t⟩
  naturality := sorry

/-- The overlap of closed complements is compatible with `restrict`. -/
theorem overlapBaseChange_comp_restrict {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    overlapBaseChange f i g ≫ restrict f i =
      restrict (f' f g) (i' i g) ≫ complementBaseChange i g :=
  sorry

/-- The overlap of closed complements is compatible with the inclusions into `Y'` and `Y`. -/
theorem overlapBaseChange_comp_ι {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    overlapBaseChange f i g ≫ closedImmersionComplementι (inverseImageι f i) =
      closedImmersionComplementι (inverseImageι (f' f g) (i' i g)) ≫ toY f g :=
  sorry

/-- Pullback along `restrict (f' f g) (i' i g)` then `complementBaseChange` identifies
with pullback along the composite. -/
def pulledBackφ_restrictComp {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (H : QCoh (closedImmersionComplement i)) :
    (pullback (restrict (f' f g) (i' i g))).obj
        ((pullback (complementBaseChange i g)).obj H) ≅
      (pullback (restrict (f' f g) (i' i g) ≫ complementBaseChange i g)).obj H :=
  (pullbackCompIso (restrict (f' f g) (i' i g)) (complementBaseChange i g)).symm.app H

/-- Transport of pullback along the overlap-restrict square. -/
def pulledBackφ_restrictEq {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (H : QCoh (closedImmersionComplement i)) :
    (pullback (restrict (f' f g) (i' i g) ≫ complementBaseChange i g)).obj H ≅
      (pullback (overlapBaseChange f i g ≫ restrict f i)).obj H :=
  eqToIso (congrArg (fun h ↦ (pullback h).obj H)
    (overlapBaseChange_comp_restrict f i g).symm)

/-- Pullback along the composite `overlapBaseChange ≫ restrict` identifies with
successive pullbacks. -/
def pulledBackφ_overlapRestrict {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (H : QCoh (closedImmersionComplement i)) :
    (pullback (overlapBaseChange f i g ≫ restrict f i)).obj H ≅
      (pullback (overlapBaseChange f i g)).obj ((pullback (restrict f i)).obj H) :=
  (pullbackCompIso (overlapBaseChange f i g) (restrict f i)).app H

/-- Pullback along the composite `overlapBaseChange ≫ closedImmersionComplementι`
identifies with successive pullbacks. -/
def pulledBackφ_overlapι {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] (G : QCoh Y) :
    (pullback (overlapBaseChange f i g)).obj
        ((pullback (closedImmersionComplementι (inverseImageι f i))).obj G) ≅
      (pullback (overlapBaseChange f i g ≫
          closedImmersionComplementι (inverseImageι f i))).obj G :=
  (pullbackCompIso (overlapBaseChange f i g)
    (closedImmersionComplementι (inverseImageι f i))).symm.app G

/-- Transport of pullback along the overlap-inclusion square. -/
def pulledBackφ_ιEq {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] (G : QCoh Y) :
    (pullback (overlapBaseChange f i g ≫
        closedImmersionComplementι (inverseImageι f i))).obj G ≅
      (pullback (closedImmersionComplementι (inverseImageι (f' f g) (i' i g)) ≫
          toY f g)).obj G :=
  eqToIso (congrArg (fun h ↦ (pullback h).obj G) (overlapBaseChange_comp_ι f i g))

/-- Pullback along `closedImmersionComplementι (inverseImageι (f' f g) (i' i g))`
then `toY` identifies with pullback along the composite. -/
def pulledBackφ_toYComp {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] (G : QCoh Y) :
    (pullback (closedImmersionComplementι (inverseImageι (f' f g) (i' i g)) ≫
        toY f g)).obj G ≅
      (pullback (closedImmersionComplementι (inverseImageι (f' f g) (i' i g)))).obj
        ((pullback (toY f g)).obj G) :=
  (pullbackCompIso (closedImmersionComplementι (inverseImageι (f' f g) (i' i g)))
    (toY f g)).app G

/-- The pulled-back glueing isomorphism of a triple `(H, G, φ)`. -/
def pulledBackφ {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    {H : QCoh (closedImmersionComplement i)} {G : QCoh Y}
    (φ : (pullback (restrict f i)).obj H ≅
      (pullback (closedImmersionComplementι (inverseImageι f i))).obj G) :
    (pullback (restrict (f' f g) (i' i g))).obj
        ((pullback (complementBaseChange i g)).obj H) ≅
      (pullback (closedImmersionComplementι (inverseImageι (f' f g) (i' i g)))).obj
        ((pullback (toY f g)).obj G) :=
  pulledBackφ_restrictComp f i g H ≪≫ pulledBackφ_restrictEq f i g H ≪≫
    pulledBackφ_overlapRestrict f i g H ≪≫
    (pullback (overlapBaseChange f i g)).mapIso φ ≪≫
    pulledBackφ_overlapι f i g G ≪≫ pulledBackφ_ιEq f i g G ≪≫
    pulledBackφ_toYComp f i g G

/-- The pullback functor `QCoh(Y → X, Z) ⥤ QCoh(Y' → X', Z')` along `g : X' ⟶ X`. -/
def baseChange {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    category f i ⥤ category (f' f g) (i' i g) where
  obj t :=
    ⟨(pullback (complementBaseChange i g)).obj t.fst,
      (pullback (toY f g)).obj t.snd, pulledBackφ f i g t.iso⟩
  map {t t'} α :=
    ⟨(pullback (complementBaseChange i g)).map α.fst,
      (pullback (toY f g)).map α.snd, sorry⟩
  map_id := sorry
  map_comp := sorry

namespace baseChange

/-- The first component of `baseChange` is quasi-coherent pullback along
`complementBaseChange`. -/
theorem obj_fst {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (t : category f i) :
    ((baseChange f i g).obj t).fst = (pullback (complementBaseChange i g)).obj t.fst :=
  rfl

/-- The second component of `baseChange` is quasi-coherent pullback along `toY`. -/
theorem obj_snd {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (t : category f i) :
    ((baseChange f i g).obj t).snd = (pullback (toY f g)).obj t.snd :=
  rfl

/-- The structural isomorphism of `baseChange` is `pulledBackφ` of the original
glueing isomorphism. -/
theorem obj_iso {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (t : category f i) :
    ((baseChange f i g).obj t).iso = pulledBackφ f i g t.iso :=
  rfl

end baseChange

end AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing

namespace AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing

/-- The comparison `V' ⟶ V` of open inverse images of the complements of `i'` and `i`. -/
def overlapBaseChange {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    V (QCoh.FormalGlueing.f' f g) (QCoh.FormalGlueing.i' i g) ⟶ V f i :=
  pullback.map (toFunctorOfPoints (QCoh.FormalGlueing.f' f g))
    (toFunctorOfPoints (j (QCoh.FormalGlueing.i' i g))) (toFunctorOfPoints f)
    (toFunctorOfPoints (j i)) (toFunctorOfPoints (QCoh.FormalGlueing.toY f g))
    (toFunctorOfPoints (QCoh.FormalGlueing.complementBaseChange i g))
    (toFunctorOfPoints g) sorry sorry

/-- Open overlap is compatible with `restrictF`. -/
theorem overlapBaseChange_comp_restrictF {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    overlapBaseChange f i g ≫ restrictF f i =
      restrictF (QCoh.FormalGlueing.f' f g) (QCoh.FormalGlueing.i' i g) ≫
        QCoh.FormalGlueing.complementBaseChange i g :=
  sorry

/-- Open overlap is compatible with the inclusions `j'`. -/
theorem overlapBaseChange_comp_j' {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    overlapBaseChange f i g ≫ j' f i =
      j' (QCoh.FormalGlueing.f' f g) (QCoh.FormalGlueing.i' i g) ≫
        QCoh.FormalGlueing.toY f g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing
