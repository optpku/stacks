module

public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv
public import ReasLib.AlgebraicTopology.SimplicialSet.DeltaOne.Endpoint
public import ReasLib.AlgebraicTopology.SimplicialSet.TrivialKanFibration
public import ReasLib.CategoryTheory.MorphismProperty.LiftingProperty.Splitting

/-!
@stack 08NS

# Trivial Kan fibrations are homotopy equivalences

Lifting against all boundary inclusions supplies a section and a simplicial-cylinder homotopy,
and therefore a simplicial homotopy equivalence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory Simplicial

universe u

namespace SSet.modelCategoryQuillen.I

namespace rlp

variable {X Y : SSet.{u}} {f : X ⟶ Y}

/-- The split-epimorphism structure selected from the initial-object lifting problem of a trivial
Kan fibration. -/
@[stacks 08NS "chosen splitting of a trivial Kan fibration"]
noncomputable def splitEpi (hf : I.rlp f) : SplitEpi f :=
  ((SSet.rlp_monomorphisms.symm.le f hf) (initial.to Y)
    (MorphismProperty.monomorphisms.infer_property _)).splitEpi

/-- The section chosen from the initial-object lifting square of a trivial Kan fibration. -/
@[stacks 08NS "chosen section of a trivial Kan fibration"]
noncomputable def sectionMap (hf : I.rlp f) : Y ⟶ X :=
  (splitEpi hf).section_

/-- The chosen section of a trivial Kan fibration is a right inverse. -/
@[reassoc (attr := simp), stacks 08NS "chosen section is a right inverse"]
theorem sectionMap_comp (hf : I.rlp f) : sectionMap hf ≫ f = 𝟙 Y := sorry

/-- The endpoint lifting square whose chosen diagonal contracts the source of a trivial Kan
fibration onto the image of its chosen section. -/
@[stacks 08NS "cylinder square for a trivial Kan fibration"]
theorem cylinderSq (hf : I.rlp f) :
    CommSq (coprod.desc (f ≫ sectionMap hf) (𝟙 X))
      (SSet.endpointInclusion X) f
      (CartesianMonoidalCategory.fst X (Δ[1] : SSet.{u}) ≫ f) := sorry

/-- The composite of a trivial Kan fibration with its chosen section is homotopic to the
identity of its source. -/
@[stacks 08NS "trivial Kan fibration homotopy from hom-inverse composite"]
theorem homotopyEquiv.hom_inv_id (hf : I.rlp f) :
    SimplicialObject.Homotopic (f ≫ sectionMap hf) (𝟙 X) := sorry

/-- The composite of the chosen section with a trivial Kan fibration is homotopic to the
identity of its target. -/
@[stacks 08NS "trivial Kan fibration homotopy from inverse-hom composite"]
theorem homotopyEquiv.inv_hom_id (hf : I.rlp f) :
    SimplicialObject.Homotopic (sectionMap hf ≫ f) (𝟙 Y) := sorry

/-- The simplicial homotopy equivalence whose forward map is a trivial Kan fibration and whose
inverse is the section chosen by its lifting property. -/
@[stacks 08NS "chosen homotopy equivalence of a trivial Kan fibration"]
noncomputable def homotopyEquiv (hf : I.rlp f) :
    SimplicialObject.HomotopyEquiv X Y where
  hom := f
  inv := sectionMap hf
  hom_inv_id := homotopyEquiv.hom_inv_id hf
  inv_hom_id := homotopyEquiv.inv_hom_id hf

/-- The forward map of the chosen trivial-Kan-fibration homotopy equivalence is the fibration
map itself. -/
@[simp, stacks 08NS "forward map of the chosen trivial Kan fibration homotopy equivalence"]
theorem homotopyEquiv.hom (hf : I.rlp f) :
    (homotopyEquiv hf).hom = f := sorry

/-- The inverse map of the chosen trivial-Kan-fibration homotopy equivalence is its selected
section. -/
@[simp, stacks 08NS "inverse map of the chosen trivial Kan fibration homotopy equivalence"]
theorem homotopyEquiv.inv (hf : I.rlp f) :
    (homotopyEquiv hf).inv = sectionMap hf := sorry

end rlp

/-- Lemma 14.30.8 (08NS): the boundary-inclusion right lifting property is contained in the
morphism property of simplicial homotopy equivalences. -/
@[stacks 08NS]
theorem rlp.le_homotopyEquivalences :
    I.rlp ≤ SimplicialObject.homotopyEquivalences (Type u) := sorry

/-- Every trivial Kan fibration of simplicial sets is a simplicial homotopy equivalence. -/
@[stacks 08NS "trivial Kan fibrations are homotopy equivalences"]
theorem rlp.isHomotopyEquivalence {X Y : SSet.{u}} {f : X ⟶ Y} (hf : I.rlp f) :
    SimplicialObject.IsHomotopyEquivalence f := sorry

end SSet.modelCategoryQuillen.I
