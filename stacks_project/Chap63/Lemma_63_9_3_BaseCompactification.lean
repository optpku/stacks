module

public import stacks_project.Chap63.Lemma_63_9_3_Codomain

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T]
  (A : AssocDiagram X g h)

/-- The C-composite and A+B base are the same geometric compactification via identity on the ambient. -/
def baseCompactificationIso :
    CompDiagram.ofComposite (Over.mk g) h A.compHG ≅ A.compF.P_g :=
  ObjectProperty.isoMk _ (Under.isoMk
    (Over.isoMk (Iso.refl A.P_g.obj.right.left) (Category.id_comp _))
    (by
      apply CostructuredArrow.hom_ext
      exact (Category.comp_id _).trans
        (CompDiagram.ιInterior_comp_openImmersion (Over.mk g) h A.compHG)))

/-- The forward geometric base transition is the identity on the ambient of g. -/
theorem baseCompactificationIso_hom_ambient :
    Of.ambientMap (baseCompactificationIso X g h A).hom = 𝟙 A.P_g.obj.right.left := rfl

/-- The reverse geometric base transition is also the literal identity. -/
theorem baseCompactificationIso_inv_ambient :
    Of.ambientMap (baseCompactificationIso X g h A).inv = 𝟙 A.P_g.obj.right.left := rfl

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end
