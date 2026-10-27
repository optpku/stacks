/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.MorphismComparison

/-!
# Lemma 96.10.3

If `f : X ⟶ Y` is a 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf` and `X`, `Y` are represented by algebraic spaces `F`, `G`,
then the square of ringed topoi with upper edge `f`, left edge `π_F`, right
edge `π_G`, and lower edge `f_small` is commutative. The source explicitly
denies a commutative diagram of ringed sites, because `F ⟶ G` need not be
representable by schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Functor FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 96.10.3: the canonical square of étale ringed topoi commutes. -/
@[stacks 073N]
#check (AlgebraicGeometry.GroupoidsOver.compareMorphism_commutes :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} {F G : AlgebraicSpace S}
      (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
      [HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type u)]
      [HasSheafify (AlgebraicSpace.smallEtaleTopology G) (Type u)]
      [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
        (smallEtaleFunctor F X eX).op.HasLeftKanExtension P]
      [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
        (smallEtaleFunctor G Y eY).op.HasLeftKanExtension P],
      -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
      letI := hasSmallCFGTypeSections_ofRepresented f eX eY
      Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
        (RingedSite.ToposHom.comp.{u + 1, u, u + 1, u, u + 1, u, u} (etaleRingedToposHom f) (piToposHom G Y eY))
        (RingedSite.ToposHom.comp.{u + 1, u, u + 1, u, u + 1, u, u} (piToposHom F X eX)
          (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)))))
