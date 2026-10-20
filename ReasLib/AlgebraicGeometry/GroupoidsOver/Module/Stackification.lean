/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.SheafEquivalence

/-!
# Invariance of module categories under stackification

Local equivalences of categories fibred in groupoids over the big fppf site
induce equivalences on module sheaves and on quasi-coherent modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)

/-- Module pullback along a local equivalence of categories fibred in groupoids
over the big fppf site is an equivalence. -/
theorem modulePullback_isEquivalence
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f) :
    (modulePullback f).IsEquivalence :=
  sorry

/-- If the pullback of a module sheaf along a local equivalence of categories
fibred in groupoids is quasi-coherent, then the sheaf is quasi-coherent. -/
theorem isQuasicoherent_of_modulePullback
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f)
    (G : SheafOfModules.{u} (structureSheaf Y))
    [((modulePullback f).obj G).IsQuasicoherent] :
    G.IsQuasicoherent :=
  sorry

/-- Quasi-coherence of a module sheaf is equivalent to quasi-coherence of its
pullback along a local equivalence of categories fibred in groupoids. -/
theorem modulePullback_isQuasicoherent_iff
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f)
    (G : SheafOfModules.{u} (structureSheaf Y)) :
    ((modulePullback f).obj G).IsQuasicoherent ↔ G.IsQuasicoherent :=
  sorry

/-- Quasi-coherent pullback along a local equivalence of categories fibred in
groupoids over the big fppf site is an equivalence. -/
theorem QCoh.pullback_isEquivalence
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f) :
    (QCoh.pullback f).IsEquivalence :=
  sorry

/-- Module pullback along a stackification morphism is an equivalence. -/
theorem modulePullback_isEquivalence_of_isStackification
    (hstack : Hom.IsStackification (Scheme.fppfTopology.over S) f) :
    (modulePullback f).IsEquivalence :=
  sorry

/-- Quasi-coherent pullback along a stackification morphism is an equivalence. -/
theorem QCoh.pullback_isEquivalence_of_isStackification
    (hstack : Hom.IsStackification (Scheme.fppfTopology.over S) f) :
    (QCoh.pullback f).IsEquivalence :=
  sorry

end AlgebraicGeometry.GroupoidsOver
