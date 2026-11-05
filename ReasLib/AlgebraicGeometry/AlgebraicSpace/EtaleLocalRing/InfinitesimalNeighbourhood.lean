/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Neighborhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion

/-! Infinitesimal neighbourhoods over the spectrum of an étale local ring. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FormalFunctions

open GeometricPoint.SmallEtaleNeighborhood
open etaleLocalRing_etaleNeighborhood

variable {S : Scheme.{u}}

/-- Use the supplied scheme atlas with its geometric-point lift as an étale neighbourhood.
This does not select a representative using the admitted site-point cofilteredness proof. -/
private def chosenNeighborhood {Y : AlgebraicSpace S} (ybar : GeometricPoint Y) :
    SmallEtaleNeighborhood ybar :=
  SmallEtaleNeighborhood.of (SmallEtale.AtlasCharts.atlasObject Y)
    (atlasLiftHom ybar) (atlasLiftHom_fac ybar)

/-- The scheme morphism `Spec(O_{Y,ȳ}) ⟶ U` through the Zariski stalk of a chosen étale
neighbourhood scheme `U` of `ȳ`. -/
private def fromSpecEtaleLocalRing_scheme {Y : AlgebraicSpace S} (ybar : GeometricPoint Y) :
    Spec (CommRingCat.of (etaleLocalRing Y ybar)) ⟶ (chosenNeighborhood ybar).scheme :=
  Spec.map
      (CommRingCat.ofHom
        (fromZariskiStalk (chosenNeighborhood ybar))) ≫
    (chosenNeighborhood ybar).scheme.fromSpecStalk (chosenNeighborhood ybar).center

/-- The structure morphism `Spec(O_{Y,ȳ}) ⟶ S`. -/
@[no_expose]
def specHom {Y : AlgebraicSpace S} (ybar : GeometricPoint Y) :
    Spec (CommRingCat.of (etaleLocalRing Y ybar)) ⟶ S :=
  fromSpecEtaleLocalRing_scheme ybar ≫ (chosenNeighborhood ybar).toSite.left.hom

/-- The algebraic space `Spec(O_{Y,ȳ})` over `S`. -/
abbrev specSpace {Y : AlgebraicSpace S} (ybar : GeometricPoint Y) : AlgebraicSpace S :=
  ofOver (Over.mk (specHom ybar))

/-- `specSpace ybar` is `ofOver` of `Spec(O_{Y,ȳ})` over `S`. -/
theorem specSpace_eq {Y : AlgebraicSpace S} (ybar : GeometricPoint Y) :
    specSpace ybar = ofOver (Over.mk (specHom ybar)) :=
  rfl

/-- Compatibility of `fromSpecEtaleLocalRing_scheme` with the structure morphism of `Y`. -/
private theorem fromSpecEtaleLocalRing_scheme_comp {Y : AlgebraicSpace S}
    (ybar : GeometricPoint Y) :
    fromSpecEtaleLocalRing_scheme ybar ≫ (chosenNeighborhood ybar).toSite.left.hom =
      specHom ybar :=
  rfl

/-- The canonical morphism `c : Spec(O_{Y,ȳ}) ⟶ Y` of algebraic spaces over `S`. -/
@[no_expose]
def fromSpecEtaleLocalRing {Y : AlgebraicSpace S} (ybar : GeometricPoint Y) :
    specSpace ybar ⟶ Y :=
  ofOverMap (Over.homMk (fromSpecEtaleLocalRing_scheme ybar)
      (fromSpecEtaleLocalRing_scheme_comp ybar)) ≫
    (chosenNeighborhood ybar).toSite.hom

/-- Compatibility of the neighbourhood factorization `Spec(O_{Y,ȳ}) ⟶ N` with `specHom`. -/
theorem fromSpecToNeighborhood_w {Y : AlgebraicSpace S} (ybar : GeometricPoint Y)
    (N : SmallEtaleNeighborhood ybar) :
    (Spec.map
          (CommRingCat.ofHom
            (fromZariskiStalk N)) ≫
        N.scheme.fromSpecStalk N.center) ≫
      N.toSite.left.hom =
      specHom ybar :=
  sorry

/-- The factorization of `Spec(O_{Y,ȳ}) ⟶ Y` through an étale neighbourhood `N` of `ȳ`. -/
def fromSpecToNeighborhood {Y : AlgebraicSpace S} (ybar : GeometricPoint Y)
    (N : SmallEtaleNeighborhood ybar) :
    specSpace ybar ⟶ ofOver N.toSite.left :=
  ofOverMap
    (Over.homMk
      (Spec.map
          (CommRingCat.ofHom
            (fromZariskiStalk N)) ≫
        N.scheme.fromSpecStalk N.center)
      (fromSpecToNeighborhood_w ybar N))

/-- On any étale neighbourhood `N` of `ȳ`, the morphism `Spec(O_{Y,ȳ}) ⟶ Y` agrees with
`Spec.map` of `fromZariskiStalk N`, postcomposed with `fromSpecStalk` of the neighbourhood
scheme and the structure morphism `N ⟶ Y`. In particular it is independent of the private
chart used to construct it, and recovers `ȳ` at the closed point. -/
theorem fromSpecEtaleLocalRing_spec {Y : AlgebraicSpace S} (ybar : GeometricPoint Y)
    (N : SmallEtaleNeighborhood ybar) :
    fromSpecEtaleLocalRing ybar =
      fromSpecToNeighborhood ybar N ≫ N.toSite.hom :=
  sorry

/-- The morphism `Spec(O_{Y,ȳ}) ⟶ Y` is flat. -/
instance instFlat_fromSpecEtaleLocalRing {Y : AlgebraicSpace S} (ybar : GeometricPoint Y) :
    Flat (fromSpecEtaleLocalRing ybar) :=
  sorry

variable {Y : AlgebraicSpace S} [IsLocallyNoetherian Y]

/-- The closed immersion `Spec(O_{Y,ȳ}/m^n) ⟶ Spec(O_{Y,ȳ})`. -/
def quotientToSpec (ybar : GeometricPoint Y) (n : ℕ) :
    Spec
        (CommRingCat.of
          (etaleLocalRing Y ybar ⧸
            IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ n)) ⟶
      Spec (CommRingCat.of (etaleLocalRing Y ybar)) :=
  @Spec.quotientMap (CommRingCat.of (etaleLocalRing Y ybar))
    (IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ n)

/-- The infinitesimal thickening `Spec(O_{Y,ȳ}/m^n)` as an algebraic space over `S`. -/
abbrev thickening (ybar : GeometricPoint Y) (n : ℕ) : AlgebraicSpace S :=
  ofOver (Over.mk (quotientToSpec ybar n ≫ specHom ybar))

/-- `thickening ybar n` is `ofOver` of `Spec(O_{Y,ȳ}/m^n)` over `S`. -/
theorem thickening_eq (ybar : GeometricPoint Y) (n : ℕ) :
    thickening ybar n = ofOver (Over.mk (quotientToSpec ybar n ≫ specHom ybar)) :=
  rfl

/-- The map `Spec(O_{Y,ȳ}/m^n) ⟶ Y` through the strict-local spectrum. -/
def toY (ybar : GeometricPoint Y) (n : ℕ) : thickening ybar n ⟶ Y :=
  ofOverHomMk (quotientToSpec ybar n) rfl ≫ fromSpecEtaleLocalRing ybar

/-- `toY ybar n` is `ofOverHomMk` of the affine quotient map, postcomposed with
`fromSpecEtaleLocalRing`. -/
theorem toY_eq (ybar : GeometricPoint Y) (n : ℕ) :
    toY ybar n = ofOverHomMk (quotientToSpec ybar n) rfl ≫ fromSpecEtaleLocalRing ybar :=
  rfl

/-- The morphism `Spec(O_{Y,ȳ}/m^n) ⟶ Spec(O_{Y,ȳ})` of algebraic spaces over `S`. -/
def toSpecSpace (ybar : GeometricPoint Y) (n : ℕ) :
    thickening ybar n ⟶ specSpace ybar :=
  ofOverHomMk (quotientToSpec ybar n) rfl

/-- `toSpecSpace` is `ofOverHomMk` of `quotientToSpec`. -/
theorem toSpecSpace_eq (ybar : GeometricPoint Y) (n : ℕ) :
    toSpecSpace ybar n = ofOverHomMk (quotientToSpec ybar n) rfl :=
  rfl

/-- The quotient transition `O_{Y,ȳ}/m^{n+1} ⟶ O_{Y,ȳ}/m^n`. -/
def quotientFactor (ybar : GeometricPoint Y) (n : ℕ) :
    etaleLocalRing Y ybar ⧸
        IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ (n + 1) →+*
      etaleLocalRing Y ybar ⧸
        IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ n :=
  Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ n))

/-- The successor quotient `O_{Y,ȳ}/m^n` is an `O_{Y,ȳ}/m^{n+1}`-algebra. -/
instance instAlgebra_quotientFactor (ybar : GeometricPoint Y) (n : ℕ) :
    Algebra
      (etaleLocalRing Y ybar ⧸
        IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ (n + 1))
      (etaleLocalRing Y ybar ⧸
        IsLocalRing.maximalIdeal (etaleLocalRing Y ybar) ^ n) :=
  (quotientFactor ybar n).toAlgebra

/-- The affine transition `Spec(O_{Y,ȳ}/m^n) ⟶ Spec(O_{Y,ȳ}/m^{n+1})` is compatible with the
structure morphisms over `S`. -/
theorem quotientFactor_specHom (ybar : GeometricPoint Y) (n : ℕ) :
    Spec.map (CommRingCat.ofHom (quotientFactor ybar n)) ≫
        quotientToSpec ybar (n + 1) ≫ specHom ybar =
      quotientToSpec ybar n ≫ specHom ybar :=
  sorry

/-- The closed immersion `Spec(O_{Y,ȳ}/m^n) ⟶ Spec(O_{Y,ȳ}/m^{n+1})` of thickenings. -/
def thickeningStep (ybar : GeometricPoint Y) (n : ℕ) :
    thickening ybar n ⟶ thickening ybar (n + 1) :=
  ofOverMap
    (Over.homMk (Spec.map (CommRingCat.ofHom (quotientFactor ybar n)))
      (quotientFactor_specHom ybar n))

/-- `thickeningStep` is `ofOverMap` of the affine quotient transition. -/
theorem thickeningStep_eq (ybar : GeometricPoint Y) (n : ℕ) :
    thickeningStep ybar n =
      ofOverMap
        (Over.homMk (Spec.map (CommRingCat.ofHom (quotientFactor ybar n)))
          (quotientFactor_specHom ybar n)) :=
  rfl

/-- The neighbourhood maps `c_n` are compatible with `thickeningStep`. -/
theorem toY_comp_thickeningStep (ybar : GeometricPoint Y) (n : ℕ) :
    thickeningStep ybar n ≫ toY ybar (n + 1) = toY ybar n :=
  sorry

variable {X : AlgebraicSpace S} (f : X ⟶ Y)

/-- The infinitesimal neighbourhood `X_n = Spec(O_{Y,ȳ}/m^n) ×_Y X`. -/
def space (ybar : GeometricPoint Y) (n : ℕ) : AlgebraicSpace S :=
  pullback f (toY ybar n)

/-- `space f ybar n` is the fibre product of `f` with `c_n`. -/
theorem space_eq_pullback (ybar : GeometricPoint Y) (n : ℕ) :
    space f ybar n = pullback f (toY ybar n) :=
  rfl

/-- The projection `i_n : X_n ⟶ X`. -/
def toX (ybar : GeometricPoint Y) (n : ℕ) : space f ybar n ⟶ X :=
  pullback.fst f (toY ybar n)

/-- `toX f ybar n` is the first projection of the neighbourhood fibre product. -/
theorem toX_eq (ybar : GeometricPoint Y) (n : ℕ) :
    toX f ybar n = pullback.fst f (toY ybar n) :=
  rfl

/-- The projection `f_n : X_n ⟶ Spec(O_{Y,ȳ}/m^n)`. -/
def toSpec (ybar : GeometricPoint Y) (n : ℕ) : space f ybar n ⟶ thickening ybar n :=
  pullback.snd f (toY ybar n)

/-- `toSpec f ybar n` is the second projection of the neighbourhood fibre product. -/
theorem toSpec_eq (ybar : GeometricPoint Y) (n : ℕ) :
    toSpec f ybar n = pullback.snd f (toY ybar n) :=
  rfl

/-- The neighbourhood square of `X_n` is a pullback. -/
theorem isPullback (ybar : GeometricPoint Y) (n : ℕ) :
    IsPullback (toX f ybar n) (toSpec f ybar n) f (toY ybar n) :=
  IsPullback.of_hasPullback f (toY ybar n)

/-- The two projections of a neighbourhood define a cone over the next stage. -/
private theorem spaceStep_condition (ybar : GeometricPoint Y) (n : ℕ) :
    toX f ybar n ≫ f =
      (toSpec f ybar n ≫ thickeningStep ybar n) ≫ toY ybar (n + 1) :=
  sorry

/-- The transition `X_n ⟶ X_{n+1}` induced by `thickeningStep`. -/
def spaceStep (ybar : GeometricPoint Y) (n : ℕ) :
    space f ybar n ⟶ space f ybar (n + 1) :=
  pullback.lift (toX f ybar n) (toSpec f ybar n ≫ thickeningStep ybar n)
    (by exact spaceStep_condition f ybar n)

/-- `spaceStep` is the pullback lift of `i_n` and `c_n` along `thickeningStep`. -/
theorem spaceStep_eq (ybar : GeometricPoint Y) (n : ℕ) :
    spaceStep f ybar n =
      pullback.lift (toX f ybar n) (toSpec f ybar n ≫ thickeningStep ybar n)
        (by exact spaceStep_condition f ybar n) :=
  rfl

/-- First projection of `spaceStep` recovers `i_n`. -/
theorem spaceStep_comp_toX (ybar : GeometricPoint Y) (n : ℕ) :
    spaceStep f ybar n ≫ toX f ybar (n + 1) = toX f ybar n :=
  sorry

/-- Second projection of `spaceStep` recovers the thickening transition. -/
theorem spaceStep_comp_toSpec (ybar : GeometricPoint Y) (n : ℕ) :
    spaceStep f ybar n ≫ toSpec f ybar (n + 1) =
      toSpec f ybar n ≫ thickeningStep ybar n :=
  sorry

/-- The pulled-back sheaf `F_n = i_n^* F`. -/
def sheaf (F : X.Modules) (ybar : GeometricPoint Y) (n : ℕ) :
    (space f ybar n).Modules :=
  (Modules.pullback (toX f ybar n)).obj F

/-- `sheaf f F ybar n` is the module pullback of `F` along `i_n`. -/
theorem sheaf_eq_pullback (F : X.Modules) (ybar : GeometricPoint Y) (n : ℕ) :
    sheaf f F ybar n = (Modules.pullback (toX f ybar n)).obj F :=
  rfl

/-- The first infinitesimal neighbourhood, over the residue field of the étale local ring. -/
abbrev fiber (ybar : GeometricPoint Y) : AlgebraicSpace S :=
  space f ybar 1

/-- The named fibre is the first infinitesimal neighbourhood. -/
theorem fiber_eq_space (ybar : GeometricPoint Y) :
    fiber f ybar = space f ybar 1 :=
  rfl

/-- The neighbourhood `X_∞ = Spec(O_{Y,ȳ}) ×_Y X`. -/
def spaceInf (ybar : GeometricPoint Y) : AlgebraicSpace S :=
  pullback f (fromSpecEtaleLocalRing ybar)

/-- `spaceInf` is the fibre product of `f` with `fromSpecEtaleLocalRing`. -/
theorem spaceInf_eq_pullback (ybar : GeometricPoint Y) :
    spaceInf f ybar = pullback f (fromSpecEtaleLocalRing ybar) :=
  rfl

/-- The projection `i_∞ : X_∞ ⟶ X`. -/
def toXInf (ybar : GeometricPoint Y) : spaceInf f ybar ⟶ X :=
  pullback.fst f (fromSpecEtaleLocalRing ybar)

/-- `toXInf` is the first projection of the `Spec(O_{Y,ȳ})` fibre product. -/
theorem toXInf_eq (ybar : GeometricPoint Y) :
    toXInf f ybar = pullback.fst f (fromSpecEtaleLocalRing ybar) :=
  rfl

/-- The projection `f_∞ : X_∞ ⟶ Spec(O_{Y,ȳ})`. -/
def toSpecInf (ybar : GeometricPoint Y) : spaceInf f ybar ⟶ specSpace ybar :=
  pullback.snd f (fromSpecEtaleLocalRing ybar)

/-- `toSpecInf` is the second projection of the `Spec(O_{Y,ȳ})` fibre product. -/
theorem toSpecInf_eq (ybar : GeometricPoint Y) :
    toSpecInf f ybar = pullback.snd f (fromSpecEtaleLocalRing ybar) :=
  rfl

/-- The neighbourhood square of `X_∞` is a pullback. -/
theorem isPullbackInf (ybar : GeometricPoint Y) :
    IsPullback (toXInf f ybar) (toSpecInf f ybar) f (fromSpecEtaleLocalRing ybar) :=
  IsPullback.of_hasPullback f (fromSpecEtaleLocalRing ybar)

/-- The pulled-back sheaf `F_∞ = i_∞^* F`. -/
def sheafInf (F : X.Modules) (ybar : GeometricPoint Y) :
    (spaceInf f ybar).Modules :=
  (Modules.pullback (toXInf f ybar)).obj F

/-- `sheafInf` is the module pullback of `F` along `i_∞`. -/
theorem sheafInf_eq_pullback (F : X.Modules) (ybar : GeometricPoint Y) :
    sheafInf f F ybar = (Modules.pullback (toXInf f ybar)).obj F :=
  rfl

/-- The projections of a neighbourhood commute over the strict-local spectrum. -/
private theorem toInf_condition (ybar : GeometricPoint Y) (n : ℕ) :
    toX f ybar n ≫ f =
      (toSpec f ybar n ≫ toSpecSpace ybar n) ≫ fromSpecEtaleLocalRing ybar :=
  sorry

/-- The closed immersion `X_n ⟶ X_∞` of infinitesimal neighbourhoods. -/
def toInf (ybar : GeometricPoint Y) (n : ℕ) :
    space f ybar n ⟶ spaceInf f ybar :=
  pullback.lift (toX f ybar n) (toSpec f ybar n ≫ toSpecSpace ybar n)
    (by exact toInf_condition f ybar n)

/-- First projection of `toInf` recovers `i_n`. -/
theorem toInf_comp_toXInf (ybar : GeometricPoint Y) (n : ℕ) :
    toInf f ybar n ≫ toXInf f ybar = toX f ybar n :=
  sorry

/-- Second projection of `toInf` recovers the thickening of `Spec(O_{Y,ȳ})`. -/
theorem toInf_comp_toSpecInf (ybar : GeometricPoint Y) (n : ℕ) :
    toInf f ybar n ≫ toSpecInf f ybar = toSpec f ybar n ≫ toSpecSpace ybar n :=
  sorry

/-- The top edge of the `Spec(O_{Y,ȳ})` square is flat, as a pullback of a flat morphism. -/
instance instFlat_toXInf (ybar : GeometricPoint Y) : Flat (toXInf f ybar) :=
  sorry

/-- Each quotient spectrum is a closed subspace of the strict-local spectrum. -/
instance instIsClosedImmersion_toSpecSpace (ybar : GeometricPoint Y) (n : ℕ) :
    IsClosedImmersion (toSpecSpace ybar n) := sorry

/-- Successive quotient spectra are related by a closed immersion. -/
instance instIsClosedImmersion_thickeningStep (ybar : GeometricPoint Y) (n : ℕ) :
    IsClosedImmersion (thickeningStep ybar n) := sorry

/-- Successive infinitesimal neighbourhoods are related by a closed immersion. -/
instance instIsClosedImmersion_spaceStep (ybar : GeometricPoint Y) (n : ℕ) :
    IsClosedImmersion (spaceStep f ybar n) := sorry

/-- Each infinitesimal neighbourhood is closed in the strict-local base change. -/
instance instIsClosedImmersion_toInf (ybar : GeometricPoint Y) (n : ℕ) :
    IsClosedImmersion (toInf f ybar n) := sorry

end FormalFunctions
end AlgebraicGeometry.AlgebraicSpace
