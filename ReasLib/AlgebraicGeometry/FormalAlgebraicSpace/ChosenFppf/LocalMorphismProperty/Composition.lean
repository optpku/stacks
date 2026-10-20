module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalMorphismProperty
public import ReasLib.RingTheory.Topology.WeaklyAdmissible.Composition

/-!
# Composition of local morphism properties of locally countably indexed spaces

Composition-stable local properties of continuous homomorphisms of countably
indexed weakly admissible rings induce composition-stable properties of
morphisms of locally countably indexed formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [hSheafify : HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [hPullbacks : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop)
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable {f : X ⟶ Y} {g : Y ⟶ Z}

include hSheafify hPullbacks

/-- Universal affine étale testing of a composition-stable local property of
continuous homomorphisms of countably indexed weakly admissible rings is
preserved by composition of morphisms of locally countably indexed formal
algebraic spaces. -/
theorem etaleAffineLocally.comp
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    [IsLocallyCountablyIndexed Z]
    (hP : IsLocalMorphismProperty P)
    (h_stable : IsStableUnderComposition P)
    (hf : etaleAffineLocally P f) (hg : etaleAffineLocally P g) :
    etaleAffineLocally P (f ≫ g) := sorry

/-- Target-cover testing of a composition-stable local property of continuous
homomorphisms of countably indexed weakly admissible rings is preserved by
composition of morphisms of locally countably indexed formal algebraic spaces. -/
theorem existsCoverOnTarget.comp
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    [IsLocallyCountablyIndexed Z]
    (hP : IsLocalMorphismProperty P)
    (h_stable : IsStableUnderComposition P)
    (hf : existsCoverOnTarget P f) (hg : existsCoverOnTarget P g) :
    existsCoverOnTarget P (f ≫ g) := sorry

/-- Source-cover testing of a composition-stable local property of continuous
homomorphisms of countably indexed weakly admissible rings is preserved by
composition of morphisms of locally countably indexed formal algebraic spaces. -/
theorem existsCoverOnSource.comp
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    [IsLocallyCountablyIndexed Z]
    (hP : IsLocalMorphismProperty P)
    (h_stable : IsStableUnderComposition P)
    (hf : existsCoverOnSource P f) (hg : existsCoverOnSource P g) :
    existsCoverOnSource P (f ≫ g) := sorry

end AlgebraicGeometry.IsLocallyCountablyIndexed
