/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.22.8: if `X` is quasi-compact and quasi-separated and `F` is a finite-type
quasi-coherent `O_X`-module, then `F` is a filtered colimit of finitely presented
`O_X`-modules with surjective transition maps. -/
@[stacks 086M] #check
  (AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_colimitPresentation_epi :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent],
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
      ∃ pres : ColimitPresentation I F,
        (∀ i : I, (pres.diag.obj i).IsFinitePresentation) ∧
          ∀ {i i' : I} (f : i ⟶ i'), Epi (pres.diag.map f))

end
