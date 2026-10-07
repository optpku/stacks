module

public import stacks_project.Chap63.Lemma_63_9_3_Compactification

/-! Concrete geometric bridges for the distinct A+B and B+C codomains. -/

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

/-- The A+B ambient map is the right-associated composite of the three proper maps. -/
theorem compositeAB_map :
    (CompDiagram.ofComposite X (g ≫ h) A.compF).obj.right.hom =
      A.P_bar.obj.right.hom ≫ (A.P_g.obj.right.hom ≫ A.P_h.obj.right.hom) := rfl

/-- The B+C ambient map is the left-associated composite of the same proper maps. -/
theorem compositeBC_map :
    (CompDiagram.ofComposite (Over.mk (X.hom ≫ g)) h A.compH).obj.right.hom =
      (A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom) ≫ A.P_h.obj.right.hom := rfl

/-- The geometric codomain comparison follows from actual category associativity. -/
theorem compositeBC_map_eq_AB :
    (CompDiagram.ofComposite (Over.mk (X.hom ≫ g)) h A.compH).obj.right.hom =
      (CompDiagram.ofComposite X (g ≫ h) A.compF).obj.right.hom :=
  Category.assoc A.P_bar.obj.right.hom A.P_g.obj.right.hom A.P_h.obj.right.hom

/-- The two ambient schemes over T are identified by the identity on the common ambient. -/
def compositeAmbientIso :
    (CompDiagram.ofComposite (Over.mk (X.hom ≫ g)) h A.compH).obj.right ≅
      (CompDiagram.ofComposite X (g ≫ h) A.compF).obj.right :=
  (Over.isoMk (Iso.refl A.P_bar.obj.right.left)
    ((Category.id_comp (A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom ≫ A.P_h.obj.right.hom)).trans
      (Category.assoc A.P_bar.obj.right.hom A.P_g.obj.right.hom A.P_h.obj.right.hom).symm) :
    Over.mk ((A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom) ≫ A.P_h.obj.right.hom) ≅
      Over.mk (A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom ≫ A.P_h.obj.right.hom))

/-- The forward ambient map is literally the identity, not a chosen inverse witness. -/
theorem compositeAmbientIso_hom_left : (compositeAmbientIso X g h A).hom.left = 𝟙 _ := rfl

/-- The reverse ambient map is also literally the identity. -/
theorem compositeAmbientIso_inv_left : (compositeAmbientIso X g h A).inv.left = 𝟙 _ := rfl

/-- The A+B interior composition is exactly the given P_bar interior. -/
theorem compositeAB_interior :
    Of.ι (CompDiagram.ofComposite X (g ≫ h) A.compF) = Of.ι A.P_bar :=
  CompDiagram.ιInterior_comp_openImmersion X (g ≫ h) A.compF

/-- The B+C interior composition is exactly the same P_bar interior. -/
theorem compositeBC_interior :
    Of.ι (CompDiagram.ofComposite (Over.mk (X.hom ≫ g)) h A.compH) = Of.ι A.P_bar :=
  CompDiagram.ιInterior_comp_openImmersion (Over.mk (X.hom ≫ g)) h A.compH

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end
