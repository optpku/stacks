/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Scalar maps to étale local rings over a field

Pullback of scalars to étale charts induces the structural field action on étale stalks.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {k : Type u} [Field k]

/-- Scalars on an étale chart are pulled back along its structural morphism to the
spectrum of the ground field. -/
def structurePresheaf.fieldMap (X : AlgebraicSpace (Spec (of k)))
    (U : smallEtaleSite X) : k →+* Γ(U.left.left, ⊤) :=
  ((Scheme.ΓSpecIso (of k)).inv ≫ U.left.hom.appTop).hom

/-- Restriction along a morphism of étale charts preserves scalar sections. -/
theorem structurePresheaf.fieldMap_naturality (X : AlgebraicSpace (Spec (of k)))
    {U V : smallEtaleSite X} (f : U ⟶ V) :
    ((structurePresheaf X).map f.op).hom.comp (structurePresheaf.fieldMap X V) =
      structurePresheaf.fieldMap X U :=
  sorry

/-- The structural field map to an étale stalk is induced by scalar sections on
all étale neighborhoods and their canonical coprojections. -/
def etaleLocalRing.algebraMapFromField {X : AlgebraicSpace (Spec (of k))}
    (xbar : GeometricPoint X) : k →+* etaleLocalRing X xbar :=
  let Φ := GeometricPoint.toSmallEtalePoint xbar
  let J := Φ.fiber.Elementsᵒᵖ
  let scalarSections : (Functor.const (smallEtaleSite X)ᵒᵖ).obj (RingCat.of k) ⟶
      structurePresheaf X :=
    { app := fun U ↦ RingCat.ofHom (structurePresheaf.fieldMap X U.unop)
      naturality := by
        intro U V f
        exact RingCat.hom_ext (by
          change (structurePresheaf.fieldMap X V.unop).comp (RingHom.id k) = _
          rw [RingHom.comp_id]
          exact (structurePresheaf.fieldMap_naturality X f.unop).symm) }
  let c : Cocone ((Functor.const J).obj (RingCat.of k)) :=
    { pt := Φ.presheafFiber.obj (structurePresheaf X)
      ι := Functor.whiskerLeft (CategoryOfElements.π Φ.fiber).op scalarSections ≫
        (colimit.cocone ((CategoryOfElements.π Φ.fiber).op ⋙ structurePresheaf X)).ι }
  (@isColimitConstCocone J _ RingCat _ (RingCat.of k)
    (IsFiltered.isConnected J)).desc c |>.hom

/-- The structural field map agrees with each scalar section germ, for every
supplied lift of the geometric point through an étale chart. -/
theorem etaleLocalRing.algebraMapFromField_germ {X : AlgebraicSpace (Spec (of k))}
    (xbar : GeometricPoint X) (U : smallEtaleSite X)
    (l : (GeometricPoint.toSmallEtalePoint xbar).fiber.obj U) :
    etaleLocalRing.algebraMapFromField xbar =
      ((GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber U l
        (structurePresheaf X)).hom.comp (structurePresheaf.fieldMap X U) :=
  sorry

/-- The étale local ring over a field is an algebra via its structural scalar map. -/
instance etaleLocalRing.instAlgebra {X : AlgebraicSpace (Spec (of k))}
    (xbar : GeometricPoint X) : Algebra k (etaleLocalRing X xbar) :=
  (etaleLocalRing.algebraMapFromField xbar).toAlgebra

/-- The algebra map to an étale local ring is its structural field map. -/
theorem etaleLocalRing.algebraMapFromField_eq {X : AlgebraicSpace (Spec (of k))}
    (xbar : GeometricPoint X) :
    algebraMap k (etaleLocalRing X xbar) = etaleLocalRing.algebraMapFromField xbar :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
