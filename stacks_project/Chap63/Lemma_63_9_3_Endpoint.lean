/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Lemma_63_9_3_Codomain

@[expose] public section
open CategoryTheory AlgebraicGeometry
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
  [CompactSpace T] [QuasiSeparatedSpace T] (A : AssocDiagram X g h)

/-- The actual A+B compactification, with right-associated structure map. -/
abbrev finalAB := CompDiagram.ofComposite X (g ≫ h) A.compF

/-- The actual B+C compactification, with left-associated structure map. -/
abbrev finalBC := CompDiagram.ofComposite (Over.mk (X.hom ≫ g)) h A.compH

/-- The ambient endpoint identification uses identity maps on the common ambient. -/
def endpointAmbientIso :
    (finalBC X g h A).obj.right.left ≅ (finalAB X g h A).obj.right.left :=
  Iso.refl A.P_bar.obj.right.left

/-- Endpoint transport preserves the actual interior X. -/
theorem endpointInterior :
    Of.ι (finalBC X g h A) ≫ (endpointAmbientIso X g h A).hom =
      Of.ι (finalAB X g h A) :=
  (Category.comp_id _).trans ((compositeBC_interior X g h A).trans
    (compositeAB_interior X g h A).symm)

/-- Endpoint transport accounts for the actual associativity of the proper structure maps. -/
theorem endpointStructure :
    (endpointAmbientIso X g h A).hom ≫ (finalAB X g h A).obj.right.hom =
      (finalBC X g h A).obj.right.hom :=
  (Category.id_comp _).trans (compositeBC_map_eq_AB X g h A).symm

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end
