module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Proper.Blowup
import StacksCheckRecall

/-!
# Isomorphisms near a closed subset after admissible blowups

A proper morphism of qcqs algebraic spaces that is an isomorphism near a
closed subset of a quasi-compact open has, after a `V`-admissible blowup, a
strict transform that is an isomorphism near the closure of that subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 81.14.3. Let `S` be a scheme. Let `f : X ⟶ Y` be a proper morphism of
quasi-compact and quasi-separated algebraic spaces over `S`. Let `V ⊂ Y` be a
quasi-compact open and `U = f⁻¹(V)`. Let `T ⊂ |V|` be a closed subset such that
`f|_U : U ⟶ V` is an isomorphism over an open neighbourhood of `T` in `V`. Then
there exists a `V`-admissible blowing up `Y' ⟶ Y` such that the strict transform
`f' : X' ⟶ Y'` of `f` is an isomorphism over an open neighbourhood of the
closure of `T` in `|Y'|`. -/
@[stacks 0F47] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isAdmissibleBlowup_strictTransform_isIso_near_closure :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [Proper f]
    (V : OpenSubspace Y) [QuasiCompact V.ι]
    (T : TopologicalSpace.Closeds (Points V.X))
    (hT : (T : Set (Points V.X)) ⊆
      isomorphismLocus (restrictTo f V)),
    ∃ (Y' : AlgebraicSpace S) (b : Y' ⟶ Y) (Z : ClosedSubspace Y)
      (h_blowup : IsBlowup b Z) (h_fp : FinitePresentation Z.ι)
      (h_disjoint : Disjoint Z.pointsSet V.pointsSet)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι),
      closure (Points.map b ⁻¹' (Points.map V.ι '' (T : Set (Points V.X)))) ⊆
        isomorphismLocus (strictTransformSnd b (Z.inverseImageSubspace b) f))

end AlgebraicGeometry.AlgebraicSpace
