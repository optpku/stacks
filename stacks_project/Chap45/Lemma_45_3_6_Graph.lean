module

public import ReasLib.AlgebraicGeometry.Correspondence.Graph

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- The source-facing graph name is an abbreviation for the canonical rational graph correspondence. -/
abbrev graphOfHom
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] (f : Y ⟶ X) :
    BivariantClass.RationalBivariantClass (fun _ ↦ 0)
      (Limits.prod.snd : X ⨯ Y ⟶ Y) 0 := rationalGraph f

end AlgebraicGeometry.Correspondence
