/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Limit.FiniteType
import ReasLib.AlgebraicGeometry.Scheme.Module.Limit.FiniteLocallyFree
import ReasLib.AlgebraicGeometry.Scheme.Module.Limit.Invertible
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 32.10.3 (1): a finite locally free module on a directed inverse limit of
quasi-compact, quasi-separated schemes with affine transition maps descends to some stage. -/
@[stacks 0B8W] #check
  (AlgebraicGeometry.Scheme.Modules.Limit.FiniteLocallyFree.exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j).carrier]
      [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (ℱ : c.pt.Modules) [ℱ.IsFiniteLocallyFree],
      ∃ (i : I) (ℱi : (D.obj i).Modules),
        ℱi.IsFiniteLocallyFree ∧
          Nonempty ((Scheme.Modules.pullback (c.π.app i)).obj ℱi ≅ ℱ))

/- Lemma 32.10.3 (2): an invertible module on a directed inverse limit of quasi-compact,
quasi-separated schemes with affine transition maps descends to an invertible module at some
stage. -/
@[stacks 0B8W] #check
  (AlgebraicGeometry.Scheme.Modules.Limit.Invertible.exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j).carrier]
      [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (ℒ : c.pt.Modules) [Scheme.Modules.Invertible ℒ],
      ∃ (i : I) (ℒi : (D.obj i).Modules),
        Scheme.Modules.Invertible ℒi ∧
          Nonempty ((Scheme.Modules.pullback (c.π.app i)).obj ℒi ≅ ℒ))

/- Lemma 32.10.3 (3): finite-type ideal-sheaf data on a directed inverse limit of
quasi-compact, quasi-separated schemes with affine transition maps descends to some stage, and
its extension to the limit is the original ideal sheaf. -/
@[stacks 0B8W] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.Limit.FiniteType.exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j).carrier]
      [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (𝓘 : c.pt.IdealSheafData) (h𝓘 : 𝓘.IsFiniteType),
      ∃ (i : I) (𝓘i : (D.obj i).IdealSheafData),
        𝓘i.IsFiniteType ∧ 𝓘i.comap (c.π.app i) = 𝓘)
