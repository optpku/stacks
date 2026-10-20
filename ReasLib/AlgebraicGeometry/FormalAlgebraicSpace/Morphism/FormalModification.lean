module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Formal modifications of locally Noetherian formal algebraic spaces

A formal modification is proper, rig-étale, and rig-surjective, and its
relative diagonal satisfies the adic complete-DVR lifting condition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A morphism of locally Noetherian formal algebraic spaces is a formal
modification when it is proper, rig-étale, and rig-surjective, and every adic
`Spf` test map into its relative diagonal lifts after an extension of complete
discrete valuation rings. -/
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
    ∀ sq : AdicSpfSquare (pullback.diagonal f), Nonempty sq.Extension

namespace FormalModification

/-- Every formal modification is a proper morphism of functors of points. -/
instance toProper {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    [hf : FormalModification f] : Proper f where
  representable := hf.representable
  of_pullback := hf.of_pullback

/-- The identity morphism of a locally Noetherian formal algebraic space is a
formal modification. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] :
    FormalModification (𝟙 X) :=
  sorry

/-- A morphism of locally Noetherian formal algebraic spaces is a formal
modification if and only if it is proper, rig-étale, and rig-surjective, and
every adic `Spf` test map into its relative diagonal lifts after an extension
of complete discrete valuation rings. -/
theorem iff_properties {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    FormalModification f ↔
      Proper f ∧ RigEtale f ∧ RigSurjective f ∧
        (∀ sq : AdicSpfSquare (pullback.diagonal f), Nonempty sq.Extension) := by
  constructor
  · intro h
    exact ⟨⟨h.representable, h.of_pullback⟩, h.toRigEtale, h.toRigSurjective,
      h.exists_extension_diagonal⟩
  · rintro ⟨hp, he, hs, hd⟩
    exact
      { toRigEtale := he
        toRigSurjective := hs
        representable := hp.representable
        of_pullback := hp.of_pullback
        exists_extension_diagonal := hd }

/-- The relative diagonal of a formal modification is rig-surjective whenever
it is locally of finite type. -/
instance rigSurjective_diagonal {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    [hf : FormalModification f] [LocallyOfFiniteType (pullback.diagonal f)] :
    RigSurjective (pullback.diagonal f) where
  exists_extension := hf.exists_extension_diagonal

end FormalModification

end AlgebraicGeometry.FormalAlgebraicSpace
