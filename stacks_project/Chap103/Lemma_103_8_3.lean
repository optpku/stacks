/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.HigherDirectImage.Restriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 103.8.3: the restriction of an étale higher direct image agrees with
the small étale higher direct image along the represented base change, after
explicit coefficient lifting. -/
@[stacks 0GQH] #check (AlgebraicGeometry.GroupoidsOver.moduleHigherDirectImage_restrictSmallEtale :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (F : etaleModules X) [IsLocallyQuasiCoherent F] [HasFlatBaseChange F]
    (y : Y.total) (U : AlgebraicSpace S) (fU : U ⟶ AlgebraicSpace.ofOver (Y.p.obj y))
    (eU : U.toGroupoids ≌ TwoFibreProduct.apex.{u + 1, u, u + 1, u} (YonedaSlice.representative (⟨y, rfl⟩ : Y.p.Fiber (Y.p.obj y))) f)
    (h_fst : eU.symm.hom ≫ AlgebraicSpace.toGroupoids.map fU ≫
      (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y)).hom ≅
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} (YonedaSlice.representative (⟨y, rfl⟩ : Y.p.Fiber (Y.p.obj y))) f)
    [aU : Abelian U.Modules] [Abelian (AlgebraicSpace.ofOver (Y.p.obj y)).Modules]
    [hI : @HasInjectiveResolutions U.Modules _ _
      (@Preadditive.preadditiveHasZeroMorphisms U.Modules _ aU.toPreadditive)] (i : ℕ),
    IsIsomorphic
      ((restrictToSmallEtaleLift Y y).obj (moduleHigherDirectImage f F i))
      ((Scheme.Etale.Small.ModuleUniverseComparison.lift (Y.p.obj y).left).obj
        (((AlgebraicSpace.schemeEtaleRingedHom (Y.p.obj y)).modulePushforward.{u}).obj
        (AlgebraicSpace.Modules.higherDirectImage fU
          (((etaleModuleInverseImage
              (TwoFibreProduct.snd.{u + 1, u, u + 1, u}
                (YonedaSlice.representative (⟨y, rfl⟩ : Y.p.Fiber (Y.p.obj y))) f)) ⋙
            (pi U _ eU).modulePushforward.{u}).obj F) i))))
