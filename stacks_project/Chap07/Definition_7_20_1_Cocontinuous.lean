module

public import ReasLib.CategoryTheory.Sites.Precoverage.Cocontinuous
public import ReasLib.CategoryTheory.Sites.PrecoverageSite

/-!
# Cocontinuity for selected precoverages

A site precoverage supplies the covering-basis hypothesis needed to pass from
selected-cover cocontinuity to cocontinuity for the generated topology.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor.Precoverage

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- A selected-cover cocontinuous functor between sites is cocontinuous for
the generated Grothendieck topologies. -/
instance IsCocontinuous.toCocontinuousOfIsSite
    {P : _root_.CategoryTheory.Precoverage C}
    {Q : _root_.CategoryTheory.Precoverage D} {u : C ⥤ D}
    [P.IsSite] [Q.IsSite] [IsCocontinuous u P Q] :
    u.IsCocontinuous P.toGrothendieck Q.toGrothendieck :=
  IsCocontinuous.toCocontinuousOfCoverBasis
    (fun hS => Precoverage.HasFactoringPullbacks.exists_generate_le (J := Q) hS)

end CategoryTheory.Functor.Precoverage
