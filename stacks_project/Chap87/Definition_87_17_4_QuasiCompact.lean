module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap87.Definition_87_25_1_Surjective

/-!
# Quasi-compact morphisms of formal algebraic spaces

A morphism of formal algebraic spaces is quasi-compact when the induced map of
algebraic-space reductions is a quasi-compact morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A morphism of formal algebraic spaces is quasi-compact if the induced map of
underlying reduced algebraic spaces is quasi-compact. -/
@[mk_iff]
class QuasiCompact {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) : Prop where
  /-- The induced map of reductions is a quasi-compact morphism of algebraic
  spaces. -/
  map_quasiCompact : AlgebraicSpace.QuasiCompact (mapReduction f)

namespace QuasiCompact

/-- The identity morphism of a formal algebraic space is quasi-compact. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X] : QuasiCompact (𝟙 X) :=
  sorry

/-- An isomorphism of formal algebraic spaces is quasi-compact. -/
instance of_isIso {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [IsIso f] : QuasiCompact f :=
  sorry

/-- A quasi-compact morphism of formal algebraic spaces induces a quasi-compact
morphism of algebraic-space reductions. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [QuasiCompact f] :
    AlgebraicSpace.QuasiCompact (mapReduction f) :=
  sorry

/-- A morphism of formal algebraic spaces is quasi-compact as soon as the induced
map of algebraic-space reductions is quasi-compact. -/
theorem of {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] {f : X ⟶ Y}
    (hf : AlgebraicSpace.QuasiCompact (mapReduction f)) : QuasiCompact f :=
  sorry

/-- A morphism of formal algebraic spaces is quasi-compact if and only if the
induced map of algebraic-space reductions is a quasi-compact morphism of
algebraic spaces. -/
theorem iff {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) :
    QuasiCompact f ↔ AlgebraicSpace.QuasiCompact (mapReduction f) :=
  sorry

end QuasiCompact

end AlgebraicGeometry.FormalAlgebraicSpace
