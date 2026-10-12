/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.OverField

@[expose] public section

open CategoryTheory DerivedCategory.TStructure

universe u

namespace AlgebraicGeometry.SchemeOverField

open RingedSpace RingedSpace.ModuleDerived

/- Example 36.35.2 (1): over a field, relative perfection for a derived module on a
finite-presentation scheme is equivalent to boundedness and pseudo-coherence. -/
@[stacks 0DI1] #check
  (AlgebraicGeometry.SchemeOverField.isPerfectOver_iff_bounded_and_pseudoCoherent :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
      [Scheme.Hom.FinitePresentation X.hom]
      (E : ModuleDerived X.left.toRingedSpace),
      IsPerfectOver X.hom.toShHom E ↔
        t.bounded E ∧ RingedSpace.ModuleDerived.IsPseudoCoherent E)

/- Example 36.35.2 (2): over a field, relative perfection for a derived module on a
finite-presentation scheme is equivalent to bounded coherent cohomology. This is a relative
condition and does not assert perfectness on every fibre. -/
@[stacks 0DI1] #check
  (AlgebraicGeometry.SchemeOverField.isPerfectOver_iff_bounded_and_coherentCohomology :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
      [Scheme.Hom.FinitePresentation X.hom]
      (E : ModuleDerived X.left.toRingedSpace),
      IsPerfectOver X.hom.toShHom E ↔
        t.bounded E ∧
          DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent (Scheme.ringCatSheaf X.left)) E)

end AlgebraicGeometry.SchemeOverField
