/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.MayerVietoris
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal

@[expose] public section

open CategoryTheory AlgebraicGeometry

/-
Lemma 20.33.4: if `U ⊔ V = ⊤`, the restriction and overlap-difference maps on open
hypercohomology fit into the five-term Mayer--Vietoris exact segment.  The reusable owner first
constructs restriction along an arbitrary inclusion `W ≤ U`, including the exact scalar-change
functor and its derived natural transformation, and then forms the two biproduct maps.  Thus the
chapter statement has no local derived-category instances or locally rebuilt restriction API.
-/

namespace AlgebraicGeometry.RingedSpace

@[stacks 08BX "Lemma 20.33.4: Mayer--Vietoris hypercohomology exact segment"]
#check @ModuleDerived.Sections.MayerVietoris.exact

/- The fine-grained restriction and displayed Mayer--Vietoris maps used by the main statement. -/
@[stacks 08BX "open-section restriction functor"]
#check @ModuleDerived.Sections.restrictionFunctor
@[stacks 08BX "derived open-section restriction"]
#check @ModuleDerived.Sections.restrictionDerived
@[stacks 08BX "open-section restriction map"]
#check @ModuleDerived.Sections.restriction
@[stacks 08BX "derived hypercohomology restriction"]
#check @ModuleDerived.Sections.hyperRestriction
@[stacks 08BX "Mayer--Vietoris biproduct map"]
#check @ModuleDerived.Sections.MayerVietoris.toBiprod
@[stacks 08BX "Mayer--Vietoris difference map"]
#check @ModuleDerived.Sections.MayerVietoris.difference

/- Companion form: derived sections over global scalars themselves form a distinguished
Mayer--Vietoris triangle. -/
@[stacks 08BX "derived sections Mayer--Vietoris triangle over global scalars"]
#check @Module.Derived.Sections.OverGlobal.mayerVietorisTriangle

end AlgebraicGeometry.RingedSpace

end
