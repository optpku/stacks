/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.BigQuasicoherent
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Properties
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped SheafOfModules.RingedSite

universe u v w

/- Lemma 35.10.4 (1): a coproduct of quasicoherent modules on a big standard
site is quasicoherent. -/
@[stacks 0GNC] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.BigQuasicoherent.coproduct :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (τ : AlgebraicGeometry.StandardTopology)
      {ι : Type v}
      (F : ι → SheafOfModules
        (AlgebraicGeometry.Scheme.AssociatedModule.bigStructureSheaf τ S))
      [HasCoproduct F] [∀ i, (F i).IsQuasicoherent],
      (∐ F).IsQuasicoherent)

/- Lemma 35.10.4 (2): quasicoherent modules on a big standard site are closed
under colimits of every universe-compatible shape. -/
@[stacks 0GNC] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.BigQuasicoherent.closedUnderColimitsOfShape :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (τ : AlgebraicGeometry.StandardTopology)
      (J : Type v) [Category.{w} J],
      IsClosedUnderColimitsOfShape
        (SheafOfModules.isQuasicoherent
          (AlgebraicGeometry.Scheme.AssociatedModule.bigStructureSheaf τ S)) J)

/- Lemma 35.10.4 (3): quasicoherent modules on a big standard site are closed
under cokernels. -/
@[stacks 0GNC] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.BigQuasicoherent.closedUnderCokernels :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (τ : AlgebraicGeometry.StandardTopology),
      (SheafOfModules.isQuasicoherent
        (AlgebraicGeometry.Scheme.AssociatedModule.bigStructureSheaf τ S)).IsClosedUnderCokernels)

/- Lemma 35.10.4 (4): quasicoherent modules on a big standard site are closed
under extensions. -/
@[stacks 0GNC] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.BigQuasicoherent.closedUnderExtensions :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (τ : AlgebraicGeometry.StandardTopology),
      (SheafOfModules.isQuasicoherent
        (AlgebraicGeometry.Scheme.AssociatedModule.bigStructureSheaf τ S)).IsClosedUnderExtensions)

section

variable (S : AlgebraicGeometry.Scheme.{u}) (τ : AlgebraicGeometry.StandardTopology)

/- Lemma 35.10.4 (5): the tensor product of two quasicoherent modules on a big
standard site is quasicoherent. -/
@[stacks 0GNC] #check
  (SheafOfModules.IsQuasicoherent.tensor
    (J := τ.overTopology S)
    (O := AlgebraicGeometry.Scheme.AssociatedModule.bigCommStructureSheaf τ S) :
    ∀ (F G : RingedSite.ModuleCat.{u + 1}
      (AlgebraicGeometry.Scheme.AssociatedModule.bigCommRingedSite τ S))
      [F.IsQuasicoherent] [G.IsQuasicoherent],
      (F ⊗ G : RingedSite.ModuleCat.{u + 1}
        (AlgebraicGeometry.Scheme.AssociatedModule.bigCommRingedSite τ S)).IsQuasicoherent)

end

/- Lemma 35.10.4 (6): internal Hom from a finite locally free module to a
quasicoherent module on a big standard site is quasicoherent. -/
@[stacks 0GNC] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.BigQuasicoherent.internalHom :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (τ : AlgebraicGeometry.StandardTopology)
      (F G : RingedSite.ModuleCat.{u + 1}
        (AlgebraicGeometry.Scheme.AssociatedModule.bigCommRingedSite τ S))
      [F.IsFiniteLocallyFree] [G.IsQuasicoherent],
      ((ihom F).obj G).IsQuasicoherent)
