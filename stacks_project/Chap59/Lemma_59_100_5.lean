module

public import stacks_project.Chap59.Lemma_59_100_5_Coefficients
public import stacks_project.Chap59.Lemma_59_100_5_Comparison
import StacksCheckRecall

@[expose] public section

/-!
Lemma 59.100.5 (0F0H) is the concrete fppf/étale comparison package on schemes.  The reusable
coefficient object is the essential image of `π_X⁻¹` on the big étale slice; the morphism class is
finite morphisms, and `ε` is the identity-site comparison from the big fppf topology to the big
étale topology.  The canonical data and the closure facts are owned by
`AlgebraicGeometry.Scheme.FppfEtale`; this chapter file is deliberately recall-only.
-/

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FppfEtale
open AlgebraicGeometry.StandardTopology
open CategoryTheory CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology
open CategoryTheory.MorphismProperty

universe u

/- Fibre products of schemes exist, so the finite morphism property has pullbacks. -/
@[stacks 0F0H "(1)"]
#check (inferInstance : MorphismProperty.HasPullbacks (@IsFinite : MorphismProperty Scheme.{u}))

/- The base change of a finite morphism of schemes is finite. -/
@[stacks 0F0H "(1)"]
#check (inferInstance : IsStableUnderBaseChange (@IsFinite : MorphismProperty Scheme.{u}))

/- The source coefficient family `A'_X = essImage (π_X⁻¹)` is a canonical object property. -/
@[stacks 0F0H "essential-image coefficient family"]
#check @essImageAb

/- The weak-Serre clause is stated on the essential-image coefficient family. -/
@[stacks 0F0H "weak Serre coefficient family"]
#check @essImageAb_isWeakSerre

/- Inverse image along a morphism preserves the essential image. -/
@[stacks 0F0H "(2)"]
#check @essImageAb_inverseImage_mem

/- Essential-image coefficients satisfy the fppf sheaf condition. -/
@[stacks 0F0H "(3)"]
#check @essImageAb_isSheafFppf

/- Higher direct images along finite morphisms remain in the essential image. -/
@[stacks 0F0H "(4)"]
#check @essImageAb_higherDirectImage_mem

/- Every fppf covering family admits an étale refinement by finite morphisms. -/
@[stacks 0F0H "(5)"]
#check @tau_covering_refinement

/- The comparison morphism `ε` from the big fppf site to the big étale site. -/
@[stacks 0F0H "comparison morphism"]
#check fun (S : Scheme.{u}) ↦ toFppf .etale S

/- Lemma 59.100.5: the five source clauses are packaged by the concrete comparison situation. -/
@[stacks 0F0H]
#check @comparisonSituation

end
