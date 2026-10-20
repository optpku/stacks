module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.NoetherianLocalMorphismProperty
public import ReasLib.RingTheory.Topology.Noetherian.Composition

/-!
# Composition of local properties of locally Noetherian formal algebraic spaces

Composition stability of local properties of continuous maps of Noetherian
adic rings passes to morphisms of locally Noetherian formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [hSheafify : HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [hPullbacks : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [hX : IsLocallyNoetherian X] [hY : IsLocallyNoetherian Y]
    [hZ : IsLocallyNoetherian Z]
variable {f : X ⟶ Y} {g : Y ⟶ Z}

include hSheafify hPullbacks hX hY hZ

/-- A local property of continuous maps of Noetherian adic rings that is stable
under composition remains stable under composition when tested on affine étale
charts of locally Noetherian formal algebraic spaces. -/
theorem etaleAffineLocally.comp (hP : Noetherian.IsLocalMorphismProperty P)
    (h_stable : Noetherian.IsStableUnderComposition P)
    (hf : etaleAffineLocally P f) (hg : etaleAffineLocally P g) :
    etaleAffineLocally P (f ≫ g) := sorry

/-- A local property of continuous maps of Noetherian adic rings that is stable
under composition remains stable under composition in the target-cover
formulation for locally Noetherian formal algebraic spaces. -/
theorem existsCoverOnTarget.comp (hP : Noetherian.IsLocalMorphismProperty P)
    (h_stable : Noetherian.IsStableUnderComposition P)
    (hf : existsCoverOnTarget P f) (hg : existsCoverOnTarget P g) :
    existsCoverOnTarget P (f ≫ g) := sorry

/-- A local property of continuous maps of Noetherian adic rings that is stable
under composition remains stable under composition in the source-cover
formulation for locally Noetherian formal algebraic spaces. -/
theorem existsCoverOnSource.comp (hP : Noetherian.IsLocalMorphismProperty P)
    (h_stable : Noetherian.IsStableUnderComposition P)
    (hf : existsCoverOnSource P f) (hg : existsCoverOnSource P g) :
    existsCoverOnSource P (f ≫ g) := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian
