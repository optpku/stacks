module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint

open CategoryTheory Opposite
open AlgebraicGeometry

@[expose] public section

universe u

variable {S : Scheme.{u}}

namespace AlgebraicGeometry.Scheme.GeometricPoint

/-- A geometric point of a scheme determines the canonical point of its small étale site. -/
noncomputable def toSmallEtalePoint (s : GeometricPoint S) :
    (smallEtaleTopology S).Point :=
  @Scheme.pointSmallEtale S s.K inferInstance
    (@IsSepClosed.of_isAlgClosed s.K inferInstance s.isAlgClosed) s.hom

end AlgebraicGeometry.Scheme.GeometricPoint

namespace AlgebraicGeometry.Scheme.Etale

/-- The stalk of a presheaf on the small étale site at a geometric point is the
presheaf fiber of the associated small-étale point, namely the colimit over
pointed étale neighborhoods. -/
noncomputable abbrev stalk (s : Scheme.GeometricPoint S)
    (F : S.Etaleᵒᵖ ⥤ Type u) : Type u :=
  (@Scheme.pointSmallEtale S s.K inferInstance
    (@IsSepClosed.of_isAlgClosed s.K inferInstance s.isAlgClosed) s.hom).presheafFiber.obj F

/-- The presheaf fiber of the canonical small-étale point at a geometric point is its geometric
étale stalk. -/
theorem pointSmallEtale_stalk (s : Scheme.GeometricPoint S)
    (F : S.Etaleᵒᵖ ⥤ Type u) :
    (@Scheme.pointSmallEtale S s.K inferInstance
      (@IsSepClosed.of_isAlgClosed s.K inferInstance s.isAlgClosed) s.hom).presheafFiber.obj F =
      Scheme.Etale.stalk s F := sorry

end AlgebraicGeometry.Scheme.Etale
