module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap87.Definition_87_30_1_Separation
public import stacks_project.Chap88.Definition_88_20_1
public import stacks_project.Chap88.Definition_88_21_1

/-!
# Formal modifications of locally Noetherian formal algebraic spaces

A morphism of locally Noetherian formal algebraic spaces is a formal
modification when it is proper, rig-étale, and rig-surjective, and its
relative diagonal is rig-surjective in the sense of adic `Spf` lifting.

`FormalAlgebraicSpace.Proper` is not a parent: that module imports
`Definition_80_4_1_Pullback`, which duplicates `pullbackSpace` already
provided by `Lemma_80_4_6` along the `RigEtale`/`RigSurjective` import path.
Properness is therefore recorded by the same Yoneda-pullback conditions as
Definition 87.31.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A morphism of locally Noetherian formal algebraic spaces is a formal
modification when it is proper in the sense of Formal Spaces,
Definition 87.31.1, rig-étale, and rig-surjective, and every adic `Spf` test
map into the relative diagonal lifts after an extension of complete discrete
valuation rings. -/
class FormalModification {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    Prop extends RigEtale f, RigSurjective f where
  /-- `f` is representable by algebraic spaces. -/
  representable : AlgebraicSpace.representableByAlgebraicSpaces f
  /-- Every Yoneda pullback of `f` is a proper morphism of algebraic spaces. -/
  of_pullback :
    ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Proper
        (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom representable ξ)
  /-- Every solid adic `Spf` square over the relative diagonal admits an
  extension of complete discrete valuation rings together with a lift. -/
  exists_extension_diagonal :
    ∀ sq : AdicSpfSquare (diagonal f), Nonempty sq.Extension

namespace FormalModification

/-- The identity morphism of a locally Noetherian formal algebraic space is a
formal modification. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] :
    FormalModification (𝟙 X) :=
  sorry

/-- A formal modification is representable by algebraic spaces, and every Yoneda
pullback is a proper morphism of algebraic spaces. -/
theorem proper {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    [hf : FormalModification f] :
    AlgebraicSpace.representableByAlgebraicSpaces f ∧
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
        AlgebraicSpace.Proper
          (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom
            hf.representable ξ) :=
  sorry

/-- A morphism of locally Noetherian formal algebraic spaces is a formal
modification if and only if it is proper in the sense of Formal Spaces,
Definition 87.31.1, rig-étale, and rig-surjective, and every adic `Spf` test
map into the relative diagonal lifts after an extension of complete discrete
valuation rings. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    FormalModification f ↔
      RigEtale f ∧ RigSurjective f ∧
        (∃ hf : AlgebraicSpace.representableByAlgebraicSpaces f,
          ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
            AlgebraicSpace.Proper
              (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom hf ξ)) ∧
        ∀ sq : AdicSpfSquare (diagonal f), Nonempty sq.Extension :=
  sorry

/-- Under locally Noetherian finite-type hypotheses on the fibre product, the
relative diagonal of a formal modification is rig-surjective. -/
theorem rigSurjective_diagonal {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    [FormalModification f] [IsFormalAlgebraicSpace (pullback f f)]
    [IsLocallyNoetherian (pullback f f)] [LocallyOfFiniteType (diagonal f)] :
    RigSurjective (diagonal f) :=
  sorry

end FormalModification

end AlgebraicGeometry.FormalAlgebraicSpace
