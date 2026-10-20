module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Ring.Ideal
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffinePresentation
public import ReasLib.AlgebraicGeometry.FormalSpectrum.Morphism
public import ReasLib.RingTheory.Topology.CountablyIndexed

/-!
# Closed immersions into countably indexed affine formal algebraic spaces

Closed immersions into countably indexed affine formal algebraic spaces preserve
countably indexed affineness and admit presentations by quotients by closed ideals.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

namespace IsCountablyIndexedAffine

/-- The source of a closed immersion of formal algebraic spaces into a countably
indexed affine formal algebraic space is countably indexed affine. -/
@[stacks 0AQI]
theorem of_closedImmersion {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsCountablyIndexedAffine X] [IsFormalAlgebraicSpace Y] (f : Y ⟶ X)
    [ClosedImmersion f] : IsCountablyIndexedAffine Y :=
  sorry

end IsCountablyIndexedAffine

/-- A closed immersion into a countably indexed affine formal algebraic space
over `S` is, under formal-spectrum presentations, induced by the canonical
quotient map of a countably indexed weakly admissible topological ring by a
closed ideal. The quotient is again weakly admissible and countably indexed,
and its quotient map is continuous. -/
@[stacks 0AQI]
theorem exists_spfMap_quotient_of_closedImmersion
    {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsCountablyIndexedAffine X] [IsFormalAlgebraicSpace Y] (f : Y ⟶ X)
    [ClosedImmersion f]
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
      (_ : TopologicalRing.IsCountablyIndexed A)
      (hA : Spec (.of A) ⟶ S) (K : Ideal A) (_ : IsClosed (K : Set A))
      (_ : TopologicalRing.IsWeaklyAdmissibleRing (A ⧸ K))
      (_ : TopologicalRing.IsCountablyIndexed (A ⧸ K))
      (hφ : Continuous (Ideal.Quotient.mk K))
      (eX : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf A hA) ≅ X)
      (eY : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj
          (spf (A ⧸ K)
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ hA)) ≅ Y),
      eY.hom ≫ f =
        (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
            (spfMap (Ideal.Quotient.mk K) hφ rfl) ≫ eX.hom :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
