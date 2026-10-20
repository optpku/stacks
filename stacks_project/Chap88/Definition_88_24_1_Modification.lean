module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap87.Definition_87_30_1_Separation
public import stacks_project.Chap88.Definition_88_20_1
public import stacks_project.Chap88.Definition_88_21_1

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FormalModification

/-!
# Formal modifications of locally Noetherian formal algebraic spaces

A morphism of locally Noetherian formal algebraic spaces is a formal
modification when it is proper, rig-étale, and rig-surjective, and its
relative diagonal is rig-surjective in the sense of adic `Spf` lifting.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

#check (AlgebraicGeometry.FormalAlgebraicSpace.FormalModification :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f], Prop)

namespace AlgebraicGeometry.FormalAlgebraicSpace.FormalModification

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
            hf.representable ξ) := by
  exact ⟨hf.representable, hf.of_pullback⟩

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
        ∀ sq : AdicSpfSquare (diagonal f), Nonempty sq.Extension := by
  constructor
  · intro hf
    exact ⟨hf.toRigEtale, hf.toRigSurjective,
      ⟨hf.representable, hf.of_pullback⟩, hf.exists_extension_diagonal⟩
  · rintro ⟨he, hs, ⟨hr, hp⟩, hd⟩
    exact (iff_properties f).mpr ⟨⟨hr, hp⟩, he, hs, hd⟩

end AlgebraicGeometry.FormalAlgebraicSpace.FormalModification
