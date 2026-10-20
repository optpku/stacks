/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap42.Lemma_42_23_6
public import ReasLib.AlgebraicGeometry.Scheme.K0.Support.Euler

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0WithSupport

/- Remark 42.56.7: for a closed immersion into a locally Noetherian scheme, the Euler
homomorphism sends a supported perfect complex to the class of its even cohomology coproduct
minus the class of its odd cohomology coproduct. -/
@[stacks 0FEP] #check
  (AlgebraicGeometry.Scheme.K0WithSupport.toCoherent_of_closedImmersion :
    ∀ {X Z : Scheme.{u}} [IsLocallyNoetherian X]
      (i : Z ⟶ X) [IsClosedImmersion i]
      (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)),
      toCoherent X (Set.range i.base) (TriangulatedK0.of E) =
        K0'WithSupport.of X (Set.range i.base)
            (evenCohomology X (Set.range i.base) E) -
          K0'WithSupport.of X (Set.range i.base)
            (oddCohomology X (Set.range i.base) E))

end AlgebraicGeometry.Scheme.K0WithSupport

#check (AlgebraicGeometry.Scheme.K0'WithSupport.closedPushforward_bijective :
  ∀ {X Z : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i],
    Function.Bijective (AlgebraicGeometry.Scheme.K0'WithSupport.closedPushforward i))
