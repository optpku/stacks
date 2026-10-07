module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap81.Lemma_81_6_2_Pushout

/-!
# Structure sheaves of pushouts along thickenings

On the identified small étale sites of a thickening `Y ⟶ Y' = Y ⨿_X X'`, the structure
sheaf of `Y'` is the fibre product of `𝒪_Y` and `f'_* 𝒪_{X'}` over `f_* 𝒪_X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening

variable {S : Scheme.{u}}

/-- The comparison map on sections of structure sheaves along an étale square. -/
def sectionMap {X Y : AlgebraicSpace S} {f : X ⟶ Y} (sq : EtaleSquare f) :
    (structureSheaf Y).obj.obj (op sq.right) ⟶ (structureSheaf X).obj.obj (op sq.left) :=
  structureFMap_app sq

/-- The section-ring map associated to a cartesian étale square with vertices `U` and `V`. -/
def sectionMap_of {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {U : smallEtaleSite X} {V : smallEtaleSite Y} (map : U.left ⟶ V.left)
    (h : IsPullback U.hom (ofOverMap map) f V.hom) :
    (structureSheaf Y).obj.obj (op V) ⟶ (structureSheaf X).obj.obj (op U) :=
  sectionMap (EtaleSquare.ofSchemeMap U V map h.w)

/-- `sectionMap_of map h` is `structureFMap_app` of the corresponding étale square. -/
theorem sectionMap_of_eq {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {U : smallEtaleSite X} {V : smallEtaleSite Y} (map : U.left ⟶ V.left)
    (h : IsPullback U.hom (ofOverMap map) f V.hom) :
    sectionMap_of map h = structureFMap_app (EtaleSquare.ofSchemeMap U V map h.w) :=
  sorry

/-- The two presentations of `V ×_{Y'} X` obtained by iterating fibre products along
`g` then `f`, and along `i'` then `i`, are isomorphic as algebraic spaces, using
`sq.w` to identify the cospans. -/
noncomputable def doublePullbackIso {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {i' : X' ⟶ Y'} {g : Y ⟶ Y'}
    (sq : CommSq i f i' g) {V : smallEtaleSite Y'} {VY : smallEtaleSite Y}
    {VX' : smallEtaleSite X'} {VX_Y VX_X' : smallEtaleSite X}
    {mapY : VY.left ⟶ V.left} {mapX' : VX'.left ⟶ V.left}
    {mapXY : VX_Y.left ⟶ VY.left} {mapXX' : VX_X'.left ⟶ VX'.left}
    (hY : IsPullback VY.hom (ofOverMap mapY) g V.hom)
    (hX' : IsPullback VX'.hom (ofOverMap mapX') i' V.hom)
    (hXY : IsPullback VX_Y.hom (ofOverMap mapXY) f VY.hom)
    (hXX' : IsPullback VX_X'.hom (ofOverMap mapXX') i VX'.hom) :
    ofOver VX_Y.left ≅ ofOver VX_X'.left :=
  let hYpath : IsPullback VX_Y.hom (ofOverMap mapXY ≫ ofOverMap mapY) (f ≫ g) V.hom :=
    IsPullback.paste_vert hXY hY
  let hXpath : IsPullback VX_X'.hom (ofOverMap mapXX' ≫ ofOverMap mapX') (i ≫ i') V.hom :=
    IsPullback.paste_vert hXX' hX'
  let hXpath' : IsPullback VX_X'.hom (ofOverMap mapXX' ≫ ofOverMap mapX') (f ≫ g) V.hom :=
    @Eq.subst (X ⟶ Y')
      (fun p ↦ IsPullback VX_X'.hom (ofOverMap mapXX' ≫ ofOverMap mapX') p V.hom)
      (i ≫ i') (f ≫ g) sq.w hXpath
  hYpath.isoIsPullback _ _ hXpath'

/-- The algebraic-space isomorphism `doublePullbackIso` identifies the structure morphisms
to `X`. -/
theorem doublePullbackIso_hom_fst {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {i' : X' ⟶ Y'} {g : Y ⟶ Y'}
    (sq : CommSq i f i' g) {V : smallEtaleSite Y'} {VY : smallEtaleSite Y}
    {VX' : smallEtaleSite X'} {VX_Y VX_X' : smallEtaleSite X}
    {mapY : VY.left ⟶ V.left} {mapX' : VX'.left ⟶ V.left}
    {mapXY : VX_Y.left ⟶ VY.left} {mapXX' : VX_X'.left ⟶ VX'.left}
    (hY : IsPullback VY.hom (ofOverMap mapY) g V.hom)
    (hX' : IsPullback VX'.hom (ofOverMap mapX') i' V.hom)
    (hXY : IsPullback VX_Y.hom (ofOverMap mapXY) f VY.hom)
    (hXX' : IsPullback VX_X'.hom (ofOverMap mapXX') i VX'.hom) :
    (doublePullbackIso sq hY hX' hXY hXX').hom ≫ VX_X'.hom = VX_Y.hom :=
  sorry

/-- A commutative square of algebraic spaces realizes `𝒪_{Y'}` as the sectionwise
pullback of `𝒪_Y` and `f'_* 𝒪_{X'}` over `f_* 𝒪_X` on canonical étale fibre products
`V ×_{Y'} Y`, `V ×_{Y'} X'`, and `V ×_{Y'} X` over every `V` in `Y'_étale`. -/
def IsStructureSheafPullback {X X' Y Y' : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) (i' : X' ⟶ Y') (g : Y ⟶ Y')
    (sq : CommSq i f i' g) : Prop :=
  ∀ (V : smallEtaleSite Y') (VY : smallEtaleSite Y) (VX' : smallEtaleSite X')
    (VX_Y VX_X' : smallEtaleSite X) (e : VX_Y ≅ VX_X')
    (mapY : VY.left ⟶ V.left) (mapX' : VX'.left ⟶ V.left)
    (mapXY : VX_Y.left ⟶ VY.left) (mapXX' : VX_X'.left ⟶ VX'.left)
    (hY : IsPullback VY.hom (ofOverMap mapY) g V.hom)
    (hX' : IsPullback VX'.hom (ofOverMap mapX') i' V.hom)
    (hXY : IsPullback VX_Y.hom (ofOverMap mapXY) f VY.hom)
    (hXX' : IsPullback VX_X'.hom (ofOverMap mapXX') i VX'.hom),
    ofOverMap e.hom.left = (doublePullbackIso sq hY hX' hXY hXX').hom →
      IsPullback (sectionMap_of mapY hY) (sectionMap_of mapX' hX')
        (sectionMap_of mapXY hXY)
        (sectionMap_of mapXX' hXX' ≫ (structureSheaf X).obj.map e.hom.op)

namespace IsStructureSheafPullback

/-- The pullback square of section rings at an étale object of `Y'`, for étale squares
presenting the canonical fibre products over that object. -/
theorem app {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {i' : X' ⟶ Y'} {g : Y ⟶ Y'} {sq : CommSq i f i' g}
    (h : IsStructureSheafPullback i f i' g sq) (V : smallEtaleSite Y')
    (VY : smallEtaleSite Y) (VX' : smallEtaleSite X')
    (VX_Y VX_X' : smallEtaleSite X) (e : VX_Y ≅ VX_X')
    (mapY : VY.left ⟶ V.left) (mapX' : VX'.left ⟶ V.left)
    (mapXY : VX_Y.left ⟶ VY.left) (mapXX' : VX_X'.left ⟶ VX'.left)
    (hY : IsPullback VY.hom (ofOverMap mapY) g V.hom)
    (hX' : IsPullback VX'.hom (ofOverMap mapX') i' V.hom)
    (hXY : IsPullback VX_Y.hom (ofOverMap mapXY) f VY.hom)
    (hXX' : IsPullback VX_X'.hom (ofOverMap mapXX') i VX'.hom)
    (he : ofOverMap e.hom.left = (doublePullbackIso sq hY hX' hXY hXX').hom) :
    IsPullback (sectionMap_of mapY hY) (sectionMap_of mapX' hX')
      (sectionMap_of mapXY hXY)
      (sectionMap_of mapXX' hXX' ≫ (structureSheaf X).obj.map e.hom.op) :=
  sorry

end IsStructureSheafPullback

/-- In any pushout of a thickening along an affine morphism, the structure sheaf of
`Y'` is the sectionwise pullback of the other three structure sheaves. -/
theorem structureSheaf_isPullback {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {i' : X' ⟶ Y'} {g : Y ⟶ Y'}
    [IsThickening i] [Affine f] (h : IsPushout i f i' g) :
    IsStructureSheafPullback i f i' g h.toCommSq :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening
