/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.Cofibered

/-!
# Smoothness after change of residue field

A smooth morphism of categories cofibered in groupoids over `C_{Λ, k}` remains
smooth after reindexing along a finite residue-field extension `k → l`.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v w

namespace ArtinianLocalAlgCat

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) (q : G ⥤ ArtinianLocalAlgCat Λ k)

noncomputable section

/-- The based morphism `F_{l/k} ⥤ᵇ G_{l/k}` over `C_{Λ, l}` induced by a based
morphism `φ : F ⥤ᵇ G` over `C_{Λ, k}`. -/
def residueChangeOverBased
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    BasedCategory.ofFunctor (residueChangeOver Λ k l p) ⥤ᵇ
      BasedCategory.ofFunctor (residueChangeOver Λ k l q) :=
  BasedFunctor.ofFunctor (residueChangeOverMap Λ k l p q φ.toFunctor φ.w) rfl

/-- The underlying functor of `residueChangeOverBased` is `residueChangeOverMap`. -/
theorem residueChangeOverBased_toFunctor
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    (residueChangeOverBased Λ k l p q φ).toFunctor =
      residueChangeOverMap Λ k l p q φ.toFunctor φ.w :=
  rfl

/-- A smooth based morphism of categories cofibered in groupoids over `C_{Λ, k}`
induces a smooth based morphism over `C_{Λ, l}` after residue-field reindexing. -/
instance instIsSmooth_residueChangeOverBased
    [Functor.IsFibered.InGroupoids p.op] [Functor.IsFibered.InGroupoids q.op]
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    [BasedFunctor.IsSmooth φ] :
    BasedFunctor.IsSmooth (residueChangeOverBased Λ k l p q φ) :=
  sorry

end

end ArtinianLocalAlgCat
