/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Lemma_63_9_1_Comparison
public import stacks_project.Chap63.Lemma_63_9_3_FirstCompactification
public import stacks_project.Chap63.Lemma_63_9_3_BaseCompactification
public import stacks_project.Chap63.Lemma_63_9_3_Pasting
public import stacks_project.Chap63.Lemma_63_9_3_Endpoint

@[expose] public section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification
noncomputable section
universe u v

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.CanonicalAssociativity

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T] (A : AssocDiagram X g h)
  (Λ : Type u) [CommRing Λ]

/-- The canonical63.9.1 transition along the first pasting isomorphism. -/
def firstTransition :=
  @isoOfHom.{u, v, v, v, v} Y X Λ inferInstance _ _
    (AssocDiagram.firstCompactificationIso X g h A).inv

/-- The canonical63.9.1 transition along the middle pasting isomorphism. -/
def midTransition :=
  @isoOfHom.{u, v, v, v, v} Z (Over.mk (X.hom ≫ g)) Λ inferInstance _ _
    (AssocDiagram.ofCompositeFG_iso_ofInteriorH X g h A).inv

/-- The canonical63.9.1 transition along the base compactification isomorphism. -/
def baseTransition :=
  @isoOfHom.{u, v, v, v, v} T (Over.mk (g ≫ h)) Λ inferInstance _ _
    (AssocDiagram.baseCompactificationIso X g h A).inv

/-- The A+B ambient over the left-associated composite, using its actual triangle. -/
def endpointAB :
    Of T (Over.mk ((X.hom ≫ g) ≫ h)) :=
  let j : Over.mk ((X.hom ≫ g) ≫ h) ⟶ (AssocDiagram.finalAB X g h A).obj.right :=
    Over.homMk (Of.ι (AssocDiagram.finalAB X g h A))
      ((Over.w (AssocDiagram.finalAB X g h A).obj.hom).trans
        (Category.assoc X.hom g h).symm)
  @Of.mk T (Over.mk ((X.hom ≫ g) ≫ h))
    (AssocDiagram.finalAB X g h A).obj.right j
    (Of.instIsOpenImmersion T (Over.mk (X.hom ≫ (g ≫ h)))
      (AssocDiagram.finalAB X g h A))
    (AssocDiagram.finalAB X g h A).property.quasiCompact
    (AssocDiagram.finalAB X g h A).property.isProper

/-- Identity on the common ambient, with the actual endpoint triangle equalities. -/
def endpointIso :
    AssocDiagram.finalBC X g h A ≅ endpointAB X g h A :=
  ObjectProperty.isoMk _ (Under.isoMk
    (AssocDiagram.compositeAmbientIso X g h A)
    (by
      apply CostructuredArrow.hom_ext
      exact (Category.comp_id _).trans
        ((AssocDiagram.compositeBC_interior X g h A).trans
          (AssocDiagram.compositeAB_interior X g h A).symm)))

/-- The canonical63.9.1 transition from the B+C endpoint to the A+B endpoint. -/
def endpointTransition :=
  @isoOfHom.{u, v, v, v, v} T (Over.mk ((X.hom ≫ g) ≫ h)) Λ inferInstance _ _
    (endpointIso X g h A).inv

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.CanonicalAssociativity
end

