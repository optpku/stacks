/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Étale morphisms between étale schemes over a base
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism between schemes that are étale over the same base is étale. -/
theorem etale_of_etale_over {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (hX : Etale X.hom) (hY : Etale Y.hom) :
    Etale f.left := sorry

end AlgebraicGeometry
