module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Equivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 94.12.4 (1): let `S` be a scheme contained in `Sch_fppf`, and let `X`,
`Y` be categories over `(Sch/S)_fppf`, formalized as objects of
`BasedCategory (Over S)`. If `X` and `Y`
are equivalent as categories over `(Sch/S)_fppf`, then `X` is an algebraic
stack if and only if `Y` is an algebraic stack. -/
@[stacks 03YQ]
#check (CategoryTheory.BasedCategory.IsAlgebraicStack.iff_of_equivalence :
  ∀ {S : Scheme.{u}} {X Y : BasedCategory.{u, u + 1} (Over S)} (e : X ≌ Y),
    BasedCategory.IsAlgebraicStack X ↔ BasedCategory.IsAlgebraicStack Y)

/- Lemma 94.12.4 (2): let `S` be a scheme contained in `Sch_fppf`, and let `X`,
`Y` be categories over `(Sch/S)_fppf`, formalized as objects of
`BasedCategory (Over S)`. If `X` and `Y`
are equivalent as categories over `(Sch/S)_fppf`, then `X` is a Deligne-Mumford
stack if and only if `Y` is a Deligne-Mumford stack. -/
@[stacks 03YQ]
#check (CategoryTheory.BasedCategory.IsDeligneMumfordStack.iff_of_equivalence :
  ∀ {S : Scheme.{u}} {X Y : BasedCategory.{u, u + 1} (Over S)} (e : X ≌ Y),
    BasedCategory.IsDeligneMumfordStack X ↔ BasedCategory.IsDeligneMumfordStack Y)
