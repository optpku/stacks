module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property

/-!
# Quasi-compact morphisms of formal algebraic spaces

Quasi-compactness is defined by the induced morphism between explicit reductions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.ReductionData

/-- A morphism of formal algebraic spaces is quasi-compact when its induced morphism
between the given reductions is quasi-compact. -/
def QuasiCompact {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) : Prop :=
  AlgebraicSpace.QuasiCompact (RX.map RY f)

/-- Quasi-compactness is equivalent to quasi-compactness of the induced reduction morphism. -/
theorem quasiCompact_iff {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    QuasiCompact RX RY f ↔ AlgebraicSpace.QuasiCompact (RX.map RY f) :=
  Iff.rfl

/-- The identity morphism is quasi-compact on a reduction. -/
theorem quasiCompact_id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (RX : ReductionData X) :
    QuasiCompact RX RX (𝟙 X) :=
  sorry

/-- An isomorphism of formal algebraic spaces is quasi-compact on their reductions. -/
theorem quasiCompact_of_isIso {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) [IsIso f] :
    QuasiCompact RX RY f :=
  sorry

/-- For a morphism of formal algebraic spaces representable by algebraic spaces,
quasi-compactness of the induced reduction morphism is equivalent to
quasi-compactness of every scheme Yoneda pullback. -/
theorem quasiCompact_iff_relativeAlgebraicSpaces {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y)
    (hf : AlgebraicSpace.representableByAlgebraicSpaces f) :
    QuasiCompact RX RY f ↔
      AlgebraicSpace.relativeAlgebraicSpaces (S := S) (@AlgebraicSpace.QuasiCompact S) f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.ReductionData
