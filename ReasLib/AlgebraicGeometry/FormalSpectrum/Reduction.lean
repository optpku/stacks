/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import ReasLib.AlgebraicGeometry.FormalSpectrum.Colimit
public import ReasLib.AlgebraicGeometry.Presheaf.Reduction
public import ReasLib.RingTheory.Topology.WeaklyAdmissible.Nilradical

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The quotient spectrum by the topological nilradical of a weakly admissible
ring is reduced. -/
instance instIsReduced_spec_topologicalNilradical {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A] :
    IsReduced (Spec (.of (A ⧸ topologicalNilradical A))) :=
  sorry

namespace FormalSpectrum

/-- The topological nilradical, bundled as a weak ideal of definition. -/
def nilradicalIdeal (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] :
    AffineFormalAlgebraicSpace.WeakIdealOfDefinition A :=
  AffineFormalAlgebraicSpace.WeakIdealOfDefinition.of (topologicalNilradical A)
    topologicalNilradical.isWeakIdealOfDefinition_of_isWeaklyAdmissible

/-- The nilradical index has the topological nilradical as its underlying ideal
and satisfies the weak-ideal condition. -/
theorem nilradicalIdeal_spec (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] :
    (nilradicalIdeal A).ideal = topologicalNilradical A ∧
      TopologicalRing.Ideal.IsWeakIdealOfDefinition (nilradicalIdeal A).ideal :=
  sorry

/-- The quotient-spectrum cocone leg into the formal spectrum. -/
def reductionι (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    yoneda.obj (AffineFormalAlgebraicSpace.stage A structureHom (nilradicalIdeal A)) ⟶
      (AffineFormalAlgebraicSpace.spf A structureHom).obj :=
  toSheafify (Scheme.fppfTopology.over S)
      (yoneda.obj (AffineFormalAlgebraicSpace.stage A structureHom (nilradicalIdeal A))) ≫
    Sheaf.homEquiv
      (AffineFormalAlgebraicSpace.spfι A structureHom (nilradicalIdeal A))

/-- The quotient-spectrum cocone leg is given by sheafification followed by the
formal-spectrum cocone map. -/
theorem reductionι_eq (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    reductionι A structureHom =
      toSheafify (Scheme.fppfTopology.over S)
          (yoneda.obj (AffineFormalAlgebraicSpace.stage A structureHom (nilradicalIdeal A))) ≫
        Sheaf.homEquiv
          (AffineFormalAlgebraicSpace.spfι A structureHom (nilradicalIdeal A)) :=
  sorry

/-- The quotient-spectrum cocone leg lands in the reduced subfunctor of the
formal spectrum. -/
theorem reductionι_range_le (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    Subfunctor.range (reductionι A structureHom) ≤
      SpacePresheaf.reduction (AffineFormalAlgebraicSpace.spf A structureHom).obj :=
  sorry

/-- The quotient spectrum maps to the reduced subfunctor of the formal spectrum. -/
def toReduction (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    yoneda.obj (AffineFormalAlgebraicSpace.stage A structureHom (nilradicalIdeal A)) ⟶
      (SpacePresheaf.reduction (AffineFormalAlgebraicSpace.spf A structureHom).obj).toFunctor :=
  Subfunctor.lift (reductionι A structureHom) (reductionι_range_le A structureHom)

/-- The comparison to the reduced subfunctor composes with its inclusion to the
quotient-spectrum cocone leg. -/
theorem toReduction_comp_ι (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    toReduction A structureHom ≫
        (SpacePresheaf.reduction (AffineFormalAlgebraicSpace.spf A structureHom).obj).ι =
      reductionι A structureHom :=
  sorry

/-- The quotient spectrum identifies with the reduced subfunctor of the formal
spectrum. -/
instance isIso_toReduction (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    IsIso (toReduction A structureHom) :=
  sorry

end FormalSpectrum

end AlgebraicGeometry
