module

public import Mathlib.CategoryTheory.Opposites
public import ReasLib.RingTheory.Etale.Category
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap87.Lemma_87_4_10_TopologicalNilradical
public import stacks_project.Chap87.Lemma_87_19_13
public import stacks_project.Chap87.Lemma_87_34_4

/-!
# Comparison of the affine étale site of `Spf(A)` with étale algebras

The affine étale site of a McQuillan affine formal algebraic space `Spf(A)`
is compared with the opposite of the category of étale `A`-algebras. The
concrete inverse direction sends an étale `A`-algebra `B` to the image of
`Spf(weakIdealCompletion A B)` in the affine étale site of the reduction.
The reduction of `Spf(A)` is `Spec(A ⧸ topologicalNilradical A)`, in the
`Reduction` interface used by Lemma 87.34.4.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace topologicalNilradical

/-- In a weakly admissible ring the topological nilradical is a weak ideal of
definition. -/
theorem isWeakIdealOfDefinition {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] :
    TopologicalRing.Ideal.IsWeakIdealOfDefinition (topologicalNilradical A) :=
  sorry

end topologicalNilradical

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The topological nilradical, bundled as a weak ideal of definition. -/
def topologicalNilradicalW (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] : WeakIdealOfDefinition A :=
  WeakIdealOfDefinition.of (topologicalNilradical A)
    topologicalNilradical.isWeakIdealOfDefinition

/-- The underlying ideal of `topologicalNilradicalW` is the topological
nilradical. -/
theorem topologicalNilradicalW_ideal (A : Type u) [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A] :
    (topologicalNilradicalW A).ideal = topologicalNilradical A :=
  sorry

/-- The algebraic space `Spec(A ⧸ topologicalNilradical A)` over `S`. -/
def specReduction (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) : AlgebraicSpace S :=
  AlgebraicSpace.ofOver (stage A structureHom (topologicalNilradicalW A))

/-- `specReduction` is the algebraic space of the affine stage at the
topological nilradical. -/
theorem specReduction_eq (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) :
    specReduction A structureHom =
      AlgebraicSpace.ofOver (stage A structureHom (topologicalNilradicalW A)) :=
  sorry

/-- The comparison morphism `Spec(A ⧸ topologicalNilradical A) ⟶ Spf(A)`
obtained from the sheafification unit and the colimit cocone of `spf`. -/
def reductionιSpf (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    (specReduction A structureHom).functorOfPoints ⟶ (spf A structureHom).obj :=
  toSheafify (Scheme.fppfTopology.over S)
      (yoneda.obj (stage A structureHom (topologicalNilradicalW A))) ≫
    Sheaf.homEquiv (spfι A structureHom (topologicalNilradicalW A))

/-- `reductionιSpf` is the sheafification unit postcomposed with the `spf`
cocone at the topological nilradical. -/
theorem reductionιSpf_eq (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    reductionιSpf A structureHom =
      toSheafify (Scheme.fppfTopology.over S)
          (yoneda.obj (stage A structureHom (topologicalNilradicalW A))) ≫
        Sheaf.homEquiv (spfι A structureHom (topologicalNilradicalW A)) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace

namespace AlgebraicGeometry.FormalAlgebraicSpace

open AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsWeaklyAdmissibleRing A] (hA : Spec (.of A) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

/-- The functor of points of an affine formal spectrum is a formal algebraic
space. -/
instance instIsFormalAlgebraicSpace_spf :
    IsFormalAlgebraicSpace (spf A hA).obj where
  isSheaf := (spf A hA).property
  exists_atlas := sorry
  exists_presentation := sorry

/-- The canonical reduction of `Spf(A)` is `Spec(A ⧸ topologicalNilradical A)`. -/
instance instReduction_spf : Reduction (spf A hA).obj where
  space := specReduction A hA
  ι := reductionιSpf A hA
  isReduced := sorry
  representable := sorry
  isThickening := sorry
  liftUnique := sorry

/-- The reduction morphism of `spf A hA` is `reductionιSpf`. -/
theorem reductionι_spf_eq : reductionι (spf A hA).obj = reductionιSpf A hA :=
  sorry

/-- The functor sending an étale `A`-algebra `B` to the object of
`AlgebraicSpace.affineEtaleSite (reduction (spf A hA).obj)` associated with
`Spf(weakIdealCompletion A B)`. -/
def spfEtaleCompletionSite :
    (CommAlgCat.Etale.{u} A)ᵒᵖ ⥤
      AlgebraicSpace.affineEtaleSite (reduction (spf A hA).obj) :=
  spfEtaleCompletion hA ⋙
    (affineEtaleOverEquiv (spf A hA).obj
      (exists_isDirectedAffineThickeningColimit_spf A hA)).functor

/-- On objects, `spfEtaleCompletionSite` is `toAffineEtale` of
`Spf(weakIdealCompletion A B)`. -/
theorem spfEtaleCompletionSite_obj (B : CommAlgCat.Etale.{u} A) :
    (spfEtaleCompletionSite hA).obj (op B) =
      toAffineEtale.obj ((spfEtaleCompletion hA).obj (op B)) :=
  sorry

/-- On morphisms, `spfEtaleCompletionSite` is `toAffineEtale` of `Spf` of
`weakIdealCompletion.map`. -/
theorem spfEtaleCompletionSite_map {B B' : CommAlgCat.Etale.{u} A} (f : B ⟶ B') :
    (spfEtaleCompletionSite hA).map f.op =
      toAffineEtale.map ((spfEtaleCompletion hA).map f.op) :=
  sorry

/-- The un-opped identification of the affine étale site of `Spf(A)` with the
opposite of the category of étale `A`-algebras. -/
def spfAffineEtaleEquiv :
    AlgebraicSpace.affineEtaleSite (reduction (spf A hA).obj) ≌
      (CommAlgCat.Etale.{u} A)ᵒᵖ :=
  (affineEtaleOverEquiv (spf A hA).obj
      (exists_isDirectedAffineThickeningColimit_spf A hA)).symm.trans
    (spfEtaleCompletion hA).asEquivalence.symm

/-- The forward functor of `spfAffineEtaleEquiv` is `ofAffineEtale` followed by
the quasi-inverse of `spfEtaleCompletion`. -/
theorem spfAffineEtaleEquiv_functor :
    (spfAffineEtaleEquiv hA).functor =
      ofAffineEtale ⋙ (spfEtaleCompletion hA).inv :=
  sorry

/-- The inverse of `spfAffineEtaleEquiv` is the concrete completion functor
`spfEtaleCompletionSite`. -/
@[simp]
theorem spfAffineEtaleEquiv_inverse :
    (spfAffineEtaleEquiv hA).inverse = spfEtaleCompletionSite hA :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace

