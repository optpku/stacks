/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.Sites.Limits
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap97.Lemma_97_11_1_Sheaf

/-!
# Base change of restriction of scalars

The identification `Res_{Z'/B'}(X') ≅ B' ×_B Res_{Z/B}(X)` of fppf sheaves on
`Sch/S`, for the chosen fibre products `Z' = B' ×_B Z` and `X' = B' ×_B X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

variable {S : Scheme.{u}} {X Z B B' : AlgebraicSpace S}

/-- The chosen fibre product `Z' = B' ×_B Z`. -/
abbrev pullbackZ (h : B' ⟶ B) (g : Z ⟶ B) : AlgebraicSpace S :=
  pullback h g

/-- The chosen fibre product `X' = B' ×_B X`, formed using the composite `X ⟶ B`. -/
abbrev pullbackX (h : B' ⟶ B) (f : X ⟶ Z) (g : Z ⟶ B) : AlgebraicSpace S :=
  pullback h (f ≫ g)

/-- The induced morphism `X' ⟶ Z'` over `B'` (and over `Z`). -/
def mapX (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    pullbackX h f g ⟶ pullbackZ h g :=
  pullback.lift (pullback.fst h (f ≫ g)) (pullback.snd h (f ≫ g) ≫ f) sorry

/-- `mapX` commutes with the projections to `B'`. -/
theorem mapX_fst (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    mapX f g h ≫ pullback.fst h g = pullback.fst h (f ≫ g) :=
  sorry

/-- `mapX` commutes with the projections to `Z` via `f`. -/
theorem mapX_snd (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    mapX f g h ≫ pullback.snd h g = pullback.snd h (f ≫ g) ≫ f :=
  sorry

/-- The induced map `X' ⟶ Z'` is the unique morphism over `B'` lifting `f`. -/
theorem mapX_spec (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    mapX f g h ≫ pullback.fst h g = pullback.fst h (f ≫ g) ∧
      mapX f g h ≫ pullback.snd h g = pullback.snd h (f ≫ g) ≫ f :=
  sorry

/-- The canonical isomorphism `T ×_{B'} Z' ≅ T ×_B Z` obtained by pasting the
fibre-product square of `Z' = B' ×_B Z`. -/
def fiberIso (h : B' ⟶ B) (g : Z ⟶ B) {T : Over S} (a' : ofOver T ⟶ B') :
    fiber (pullback.fst h g) a' ≅ fiber g (a' ≫ h) :=
  fiberIsoPullback (pullback.fst h g) a' ≪≫
    pullbackRightPullbackFstIso h g a' ≪≫
    (fiberIsoPullback g (a' ≫ h)).symm

/-- `fiberIso` identifies the projections to `T`. -/
theorem fiberIso_fst (h : B' ⟶ B) (g : Z ⟶ B) {T : Over S} (a' : ofOver T ⟶ B') :
    (fiberIso h g a').hom ≫ fiberFst g (a' ≫ h) =
      fiberFst (pullback.fst h g) a' :=
  sorry

/-- `fiberIso` identifies the projections to `Z`. -/
theorem fiberIso_snd (h : B' ⟶ B) (g : Z ⟶ B) {T : Over S} (a' : ofOver T ⟶ B') :
    (fiberIso h g a').hom ≫ fiberSnd g (a' ≫ h) =
      fiberSnd (pullback.fst h g) a' ≫ pullback.snd h g :=
  sorry

/-- The forward functor-of-points map, sending a pair over `B'` to the pair over
`B` with base `a' ≫ h` and lift transported along `fiberIso`. -/
def pairMap (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (p : Pair (mapX f g h) (pullback.fst h g) T) : Pair f g T where
  base := p.base ≫ h
  lift := (fiberIso h g p.base).inv ≫ p.lift ≫ pullback.snd h (f ≫ g)
  overZ := sorry

/-- The inverse functor-of-points map, reconstructing a pair over `B'` from a
`B'`-point and a compatible restriction-of-scalars pair over `B`. -/
def pairInv (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (a' : ofOver T ⟶ B') (q : Pair f g T) (hq : a' ≫ h = q.base) :
    Pair (mapX f g h) (pullback.fst h g) T where
  base := a'
  lift :=
    pullback.lift (fiberFst (pullback.fst h g) a' ≫ a')
      ((fiberIso h g a').hom ≫ (eqToHom (congrArg (fiber g) hq) ≫ q.lift)) sorry
  overZ := sorry

/-- Equality of `Res_{Z'/B'}(X')` and `B' ×_B Res_{Z/B}(X)` as functors of
points, recorded as an equivalence on pairs. -/
def pairEquiv (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) (T : Over S) :
    Pair (mapX f g h) (pullback.fst h g) T ≃
      { p : (ofOver T ⟶ B') × Pair f g T // p.1 ≫ h = p.2.base } where
  toFun p := ⟨⟨p.base, pairMap f g h p⟩, rfl⟩
  invFun p := pairInv f g h p.1.1 p.1.2 p.2
  left_inv := sorry
  right_inv := sorry

/-- `pairEquiv` sends a pair to its `B'`-point together with `pairMap`. -/
theorem pairEquiv_apply (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (p : Pair (mapX f g h) (pullback.fst h g) T) :
    (pairEquiv f g h T p).1 = ⟨p.base, pairMap f g h p⟩ :=
  sorry

/-- The inverse of `pairEquiv` is `pairInv` on a compatible pair of points. -/
theorem pairEquiv_symm_apply (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) {T : Over S}
    (p : (ofOver T ⟶ B') × Pair f g T) (hp : p.1 ≫ h = p.2.base) :
    (pairEquiv f g h T).symm ⟨p, hp⟩ = pairInv f g h p.1 p.2 hp :=
  sorry

/-- The sheaf morphism `Res_{Z'/B'}(X') ⟶ Res_{Z/B}(X)` induced by `pairMap`. -/
def toRestrictionOfScalars (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    restrictionOfScalarsSheaf (mapX f g h) (pullback.fst h g) ⟶
      restrictionOfScalarsSheaf f g :=
  Sheaf.homEquiv.symm
    { app T := TypeCat.ofHom (pairMap f g h)
      naturality := sorry }

/-- Components of `toRestrictionOfScalars` are `pairMap`. -/
theorem toRestrictionOfScalars_app (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B)
    (T : (Over S)ᵒᵖ) (p : Pair (mapX f g h) (pullback.fst h g) T.unop) :
    (toRestrictionOfScalars f g h).hom.app T p = pairMap f g h p :=
  sorry

/-- The inverse sheaf morphism of `pullbackIso`, reconstructed objectwise by
`pairInv` from the projections of the chosen sheaf fibre product. -/
def pullbackIso_inv (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    pullback (uliftSheafMap h) (toUliftSheaf f g) ⟶
      restrictionOfScalarsSheaf (mapX f g h) (pullback.fst h g) :=
  Sheaf.homEquiv.symm
    { app T :=
        TypeCat.ofHom fun x ↦
          pairInv f g h
            (yonedaEquiv.symm
              ((pullback.fst (uliftSheafMap h) (toUliftSheaf f g)).hom.app T x).down)
            ((pullback.snd (uliftSheafMap h) (toUliftSheaf f g)).hom.app T x) sorry
      naturality := sorry }

/-- The canonical isomorphism `Res_{Z'/B'}(X') ≅ B' ×_B Res_{Z/B}(X)` of fppf
sheaves on `Sch/S`. -/
def pullbackIso (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    restrictionOfScalarsSheaf (mapX f g h) (pullback.fst h g) ≅
      pullback (uliftSheafMap h) (toUliftSheaf f g) where
  hom :=
    pullback.lift (toUliftSheaf (mapX f g h) (pullback.fst h g))
      (toRestrictionOfScalars f g h) sorry
  inv := pullbackIso_inv f g h
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The first projection of `pullbackIso.hom` is the structure map of
`Res_{Z'/B'}(X')`. -/
theorem pullbackIso_hom_fst (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    (pullbackIso f g h).hom ≫ pullback.fst (uliftSheafMap h) (toUliftSheaf f g) =
      toUliftSheaf (mapX f g h) (pullback.fst h g) :=
  sorry

/-- The second projection of `pullbackIso.hom` is `toRestrictionOfScalars`. -/
theorem pullbackIso_hom_snd (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    (pullbackIso f g h).hom ≫ pullback.snd (uliftSheafMap h) (toUliftSheaf f g) =
      toRestrictionOfScalars f g h :=
  sorry

/-- The square relating `Res_{Z'/B'}(X')` to `Res_{Z/B}(X)` over `B' ⟶ B` is
cartesian in fppf sheaves on `Sch/S`. -/
theorem isPullback (f : X ⟶ Z) (g : Z ⟶ B) (h : B' ⟶ B) :
    IsPullback (toUliftSheaf (mapX f g h) (pullback.fst h g))
      (toRestrictionOfScalars f g h) (uliftSheafMap h) (toUliftSheaf f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
