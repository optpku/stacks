module

public import stacks_project.Chap63.Lemma_63_9_4_Transport
public import stacks_project.Chap63.Lemma_63_9_3_FirstCompactification
public import stacks_project.Chap63.Lemma_63_9_3_BaseCompactification
public import stacks_project.Chap63.Lemma_63_9_3_Pasting
public import stacks_project.Chap63.Lemma_63_9_3_Endpoint

/-! Model transport induced by the specified geometric isomorphisms of the
associativity diagram. Forward and reverse maps are the actual ambient/interior
mate composites, rather than a choice of an unspecified natural isomorphism. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.Associativity

/-- The fixed ambient-isomorphism transport between two compactification models. -/
def modelOfGeometricIso {Y : Scheme.{u}} {X : Over Y} {P Q : Of Y X} (e : P ≅ Q) :=
  @CompactificationTransport.modelIso X.left Y P.obj.right.left Q.obj.right.left
    (Of.ι P) P.obj.right.hom (Of.ι Q) Q.obj.right.hom (Of.ambientIso e.symm)
    (Of.ambientIso_interior e.symm) (Of.ambientIso_over e.symm)

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T] (A : AssocDiagram X g h)

/-- Transport from the A-interior model of f to the A+B-interior model of f. -/
def firstModelIso := modelOfGeometricIso (AssocDiagram.firstCompactificationIso X g h A)

/-- Transport from the A-composite model of gf to the B+C-interior model. -/
def midModelIso := modelOfGeometricIso (AssocDiagram.ofCompositeFG_iso_ofInteriorH X g h A)

/-- Transport from the C-composite model of hg to the A+B-base model. -/
def baseModelIso := modelOfGeometricIso (AssocDiagram.baseCompactificationIso X g h A)

/-- The endpoint transport keeps A+B and B+C's distinct structure-map associations. -/
def endpointModelIso :=
  @CompactificationTransport.modelIso X.left T A.P_bar.obj.right.left A.P_bar.obj.right.left
    (Of.ι (AssocDiagram.finalAB X g h A)) (AssocDiagram.finalAB X g h A).obj.right.hom
    (Of.ι (AssocDiagram.finalBC X g h A)) (AssocDiagram.finalBC X g h A).obj.right.hom
    (AssocDiagram.endpointAmbientIso X g h A) (AssocDiagram.endpointInterior X g h A)
    (AssocDiagram.endpointStructure X g h A)

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.Associativity
end
