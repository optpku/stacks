/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.SchemeComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Composition
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry.AlgebraicSpace Limits
open AlgebraicGeometry (Scheme)

noncomputable section

universe u

section schemeImmersion

variable {S : Scheme.{u}}
variable {Z X : Over S} (i : Z ⟶ X) [AlgebraicGeometry.IsImmersion i.left]

/- Lemma 76.5.4 (1): Let `S` be a scheme. If `i : Z ⟶ X` is an immersion of
schemes over `S`, then the algebraic-space conormal sheaf of Definition 76.5.1
agrees with `Scheme.Hom.conormalSheaf` from Morphisms, Definition 29.31.1, after
`Modules.restrictToScheme`. -/
@[stacks 04G2]
#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.restrictToSchemeIso i :
    (Modules.restrictToScheme Z).obj (Hom.conormalSheaf (ofOverMap i)) ≅
      Scheme.Hom.conormalSheaf i.left)

end schemeImmersion

section schemeSquare

variable {S : Scheme.{u}}
variable {Z X Z' X' : Over S}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
variable [AlgebraicGeometry.IsImmersion i.left] [AlgebraicGeometry.IsImmersion i'.left]
variable (sq : CommSq f i i' g)

/- Lemma 76.5.4 (2): If in Lemma 76.5.3 all the spaces are schemes, then the map
`(Modules.pullback f).obj (Hom.conormalSheaf i') ⟶ Hom.conormalSheaf i` is the same
as the one constructed in Morphisms, Lemma 29.31.3. -/
@[stacks 04G2]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.map_restrictToScheme sq :
  (Hom.Conormal.pullbackRestrictIso f i').hom ≫ Scheme.Hom.Conormal.map (ofOverSqLeft sq) =
    (Modules.restrictToScheme Z).map (Hom.Conormal.map (ofOverCommSq sq)) ≫
      (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.restrictToSchemeIso i).hom)

end schemeSquare

section stackedSquares

variable {S : Scheme.{u}}
variable {Z X Z' X' Z'' X'' : AlgebraicGeometry.AlgebraicSpace S}
variable {f : Z ⟶ Z'} {f' : Z' ⟶ Z''}
variable {i : Z ⟶ X} {i' : Z' ⟶ X'} {i'' : Z'' ⟶ X''}
variable {g : X ⟶ X'} {g' : X' ⟶ X''}
variable [IsImmersion i] [IsImmersion i'] [IsImmersion i'']
variable (sq : CommSq f i i' g) (sq' : CommSq f' i' i'' g')

/- Lemma 76.5.4 (3): Given a vertically stacked pair of commutative squares of
algebraic spaces over `S` whose horizontal arrows are immersions, the map
`(Modules.pullback (f ≫ f')).obj (Hom.conormalSheaf i'') ⟶ Hom.conormalSheaf i`
is the composition of `Hom.Conormal.map sq` with the pullback by `f` of
`Hom.Conormal.map sq'`. -/
@[stacks 04G2]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.map_comp sq sq' :
  Hom.Conormal.map (sq.horiz_comp sq') =
    (Modules.pullbackCompIso f f').inv.app (Hom.conormalSheaf i'') ≫
      (Modules.pullback f).map (Hom.Conormal.map sq') ≫ Hom.Conormal.map sq)

end stackedSquares
