module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.BaseChange

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/- Universal preservation of the structure sheaf under scheme-valued base change. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.IsIsoBaseChangeStructurePushforward :
  (X ⟶ B) → Prop)

/- Pointwise interpretation of universal preservation of the structure sheaf. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.isIsoBaseChangeStructurePushforward_iff :
  ∀ (f : X ⟶ B), Hom.IsIsoBaseChangeStructurePushforward f ↔
    ∀ τ : CohStack.SchemesOver B,
      IsIso (structureSheafMap (CohStack.fiberToBase f τ)))
