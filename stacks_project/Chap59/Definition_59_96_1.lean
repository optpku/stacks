/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.CohomologicalDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Definition 59.96.1: for a quasi-compact and quasi-separated morphism of schemes, the
cohomological dimension is the smallest element of `WithTop ℕ` for which every higher direct
image `Rⁱ f_* F` of an abelian torsion sheaf on `Xₑₜ` vanishes in degrees above the bound. -/
@[stacks 0F0Z] #check (AlgebraicGeometry.Scheme.Hom.cohomologicalDimension :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})], WithTop ℕ)
