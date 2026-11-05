/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Associativity.Diagram
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Associativity.PastingIso

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
    (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h A.compH).obj.right.hom =
      (A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom) ≫ A.P_h.obj.right.hom := rfl

/-- The geometric codomain comparison follows from actual category associativity. -/
theorem compositeBC_map_eq_AB :
    (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h A.compH).obj.right.hom =
      (CompDiagram.ofComposite X (g ≫ h) A.compF).obj.right.hom :=
  Category.assoc A.P_bar.obj.right.hom A.P_g.obj.right.hom A.P_h.obj.right.hom

/-- The two ambient schemes over T are identified by the identity on the common ambient. -/
def compositeAmbientIso :
    (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h A.compH).obj.right ≅
      (CompDiagram.ofComposite X (g ≫ h) A.compF).obj.right :=
  (Over.isoMk (Iso.refl A.P_bar.obj.right.left)
    ((Category.id_comp (A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom ≫ A.P_h.obj.right.hom)).trans
      (Category.assoc A.P_bar.obj.right.hom A.P_g.obj.right.hom A.P_h.obj.right.hom).symm) :
    Over.mk ((A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom) ≫ A.P_h.obj.right.hom) ≅
      Over.mk (A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom ≫ A.P_h.obj.right.hom))

/-- The forward ambient map is literally the identity, on the common ambient. -/
theorem compositeAmbientIso_hom_left : (compositeAmbientIso X g h A).hom.left = 𝟙 _ := rfl

/-- The reverse ambient map is also literally the identity. -/
theorem compositeAmbientIso_inv_left : (compositeAmbientIso X g h A).inv.left = 𝟙 _ := rfl

/-- The A+B interior composition is exactly the given P_bar interior. -/
theorem compositeAB_interior :
    Of.ι (CompDiagram.ofComposite X (g ≫ h) A.compF) = Of.ι A.P_bar :=
  CompDiagram.ιInterior_comp_openImmersion X (g ≫ h) A.compF

/-- The B+C interior composition is exactly the same P_bar interior. -/
theorem compositeBC_interior :
    Of.ι (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h A.compH) = Of.ι A.P_bar :=
  CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h A.compH

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end

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
    CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG ≅ A.compF.P_g :=
  ObjectProperty.isoMk _ (Under.isoMk
    (Over.isoMk (Iso.refl A.P_g.obj.right.left) (Category.id_comp _))
    (by
      apply CostructuredArrow.hom_ext
      exact (Category.comp_id _).trans
        (CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG)))

/-- The forward geometric base transition is the identity on the ambient of g. -/
theorem baseCompactificationIso_hom_ambient :
    Of.ambientMap (baseCompactificationIso X g h A).hom = 𝟙 A.P_g.obj.right.left := rfl

/-- The reverse geometric base transition is also the literal identity. -/
theorem baseCompactificationIso_inv_ambient :
    Of.ambientMap (baseCompactificationIso X g h A).inv = 𝟙 A.P_g.obj.right.left := rfl

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end

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
abbrev finalBC := CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h A.compH

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end

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

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.CanonicalAssociativity
end
