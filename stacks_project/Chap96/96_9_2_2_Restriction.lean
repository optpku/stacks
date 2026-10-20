module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SheafRestriction

/-!
# Small-étale sheaf restriction along an object of a groupoid fibration

An étale sheaf on a category fibred in groupoids restricts along an object
`x` to a sheaf on the small étale site of `U = p(x)`, by packaging the
presheaf restriction `restrictSmallEtale`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

variable (F : Sheaf X.etaleTopology (Type (u + 1))) (x : X.total)

#check (AlgebraicGeometry.GroupoidsOver.restrictSmallEtaleSheaf F x :
    Sheaf (X.p.obj x).left.smallEtaleTopology (Type (u + 1)))

#check (AlgebraicGeometry.GroupoidsOver.restrictSmallEtaleSheaf_obj F x :
    (restrictSmallEtaleSheaf F x).obj = restrictSmallEtale x F.obj)

end AlgebraicGeometry.GroupoidsOver
