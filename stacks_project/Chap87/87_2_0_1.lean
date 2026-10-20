module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Hom
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/-
87.2.0.1 Morphisms in LTRS from (Spf B, O_Spf B) to (Spf A, O_Spf A) are identified
with continuous ring homomorphisms Hom_cont(A, B).
-/
@[stacks 0AHZ]
#check (AlgebraicGeometry.FormalSpectrum.homEquiv :
  ∀ (A B : Type u) [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdmissibleRing A]
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdmissibleRing B],
    AlgebraicGeometry.LocallyTopologicallyRingedSpaceCat.Hom
      (AlgebraicGeometry.FormalSpectrum.spf B) (AlgebraicGeometry.FormalSpectrum.spf A) ≃
      (TopCommRingCat.of A ⟶ TopCommRingCat.of B))
