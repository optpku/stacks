/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Covering
public import ReasLib.AlgebraicGeometry.GroupoidsOver.CoveringLift

/-!
# Covering by essential image from geometric covering lifts

A 1-morphism that admits a `τ`-covering lift of every object covers by
essential image on the associated `τ`-site. Smooth surjective morphisms
do so étale-locally; surjective flat morphisms locally of finite presentation
do so fppf-locally.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- If every object of `𝒳` admits a `τ`-covering lift along `f`, then `f`
covers by essential image in the associated `τ`-topology. -/
theorem coversByEssentialImage_of_existsCoveringLift (f : U ⟶ X)
    (τ : StandardTopology)
    (hf : ∀ {V : Over S} (y : GroupoidsOver.slice V ⟶ X),
      Groupoids.Hom.existsCoveringLift τ f y) :
    coversByEssentialImage f τ :=
  sorry

/-- A 1-morphism representable by algebraic spaces, surjective, and smooth
covers by essential image in the associated étale topology. -/
theorem coversByEssentialImage_etale (f : U ⟶ X)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Smooth f] :
    coversByEssentialImage f StandardTopology.etale :=
  sorry

/-- A 1-morphism representable by algebraic spaces, surjective, flat, and
locally of finite presentation covers by essential image in the associated
fppf topology. -/
theorem coversByEssentialImage_fppf (f : U ⟶ X)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f] :
    coversByEssentialImage f StandardTopology.fppf :=
  sorry

end AlgebraicGeometry.GroupoidsOver
