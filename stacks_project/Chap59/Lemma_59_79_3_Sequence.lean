/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.SupportSequence

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Compatibility check for the shared étale support-sequence construction. -/
#check (Scheme.Etale.Support.sequence :
  ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (_ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
    ComposableArrows (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 5)

/- Compatibility check for the shared higher direct-image comparison. -/
#check (Scheme.Etale.Support.higherDirectImageIso :
  ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (degree : ℕ) (_ : 1 ≤ degree),
    ((Scheme.Etale.Abelian.directImage (closedImmersionComplement i).ι).rightDerived degree).obj
      ((Scheme.Etale.Abelian.inverseImage (closedImmersionComplement i).ι).obj F) ≅
    (Scheme.Etale.Abelian.directImage i).obj
      (((Scheme.Etale.Support.onClosed i).rightDerived (degree + 1)).obj F))

end AlgebraicGeometry
