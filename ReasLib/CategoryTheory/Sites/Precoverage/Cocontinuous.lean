/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# Cocontinuity for selected precoverages

A functor of precoverages is cocontinuous when every selected covering of an
image object is refined by the image of some selected covering of the source
object. The image family need not itself be covering in the target.
-/

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃ w

namespace CategoryTheory.Functor.Precoverage

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- A functor of precoverages is cocontinuous when every selected covering of
`u.obj U` is refined by the image of some selected covering of `U`. -/
class IsCocontinuous (u : C ⥤ D) (P : _root_.CategoryTheory.Precoverage C)
    (Q : _root_.CategoryTheory.Precoverage D) : Prop where
  /-- A covering of `u.obj U` is refined by the image of a covering of `U`. -/
  exists_refinement :
    ∀ ⦃U : C⦄ {R : Presieve (u.obj U)},
      R ∈ Q (u.obj U) → ∃ S : Presieve U, S ∈ P U ∧ (S.map u).FactorsThru R

namespace IsCocontinuous

variable {P : _root_.CategoryTheory.Precoverage C}
variable {Q : _root_.CategoryTheory.Precoverage D} {u : C ⥤ D}

/-- Every selected target family over `u.obj U` admits a selected source family
over `U` whose image family refines it. -/
theorem exists_cover [IsCocontinuous u P Q] {U : C} {I : Type w}
    (V : I → D) (f : ∀ i, V i ⟶ u.obj U)
    (hV : Presieve.ofArrows V f ∈ Q (u.obj U)) :
    ∃ (K : Type (max u₁ v₁)) (W : K → C) (g : ∀ k, W k ⟶ U),
      Presieve.ofArrows W g ∈ P U ∧
        ((Presieve.ofArrows W g).map u).FactorsThru (Presieve.ofArrows V f) :=
  sorry

/-- The identity functor is cocontinuous for every precoverage. -/
instance id (J : _root_.CategoryTheory.Precoverage C) :
    IsCocontinuous (𝟭 C) J J :=
  sorry

/-- The composition of cocontinuous functors of precoverages is cocontinuous. -/
theorem comp {E : Type u₃} [Category.{v₃} E] {v : D ⥤ E}
    {R : _root_.CategoryTheory.Precoverage E}
    [IsCocontinuous u P Q] [IsCocontinuous v Q R] :
    IsCocontinuous (u ⋙ v) P R :=
  sorry

/-- Selected-cover cocontinuity induces cocontinuity of the generated
Grothendieck topologies when target covers have selected refinements. -/
theorem toCocontinuousOfCoverBasis [IsCocontinuous u P Q]
    (hQ : ∀ {V : D} {T : Sieve V}, T ∈ Q.toGrothendieck V →
      ∃ R ∈ Q V, Sieve.generate R ≤ T) :
    u.IsCocontinuous P.toGrothendieck Q.toGrothendieck :=
  sorry

/-- Cocontinuity for generated Grothendieck topologies implies selected-cover
cocontinuity when source covers have selected refinements. -/
theorem ofGrothendieckOfCoverBasis
    [u.IsCocontinuous P.toGrothendieck Q.toGrothendieck]
    (hP : ∀ {U : C} {R : Sieve U}, R ∈ P.toGrothendieck U →
      ∃ S ∈ P U, Sieve.generate S ≤ R) :
    IsCocontinuous u P Q :=
  sorry

end IsCocontinuous

end CategoryTheory.Functor.Precoverage
