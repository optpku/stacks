module

import stacks_project.Chap39.Lemma_39_21_2_Comparison

open CategoryTheory Limits

universe u

namespace Scratch39_21_2

open AlgebraicGeometry
open GroupoidScheme
open GroupoidScheme.CartesianOver

theorem actionIdentity_condition_test {S : Scheme.{u}} {G : GroupoidScheme S}
    (A : GroupoidScheme.Action G) :
    𝟙 (GroupoidScheme.Action.obj A).left ≫ (GroupoidScheme.Action.obj A).hom =
      ((GroupoidScheme.Action.obj A).hom ≫ G.e) ≫ G.t := by
  simp

end Scratch39_21_2
