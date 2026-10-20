/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.Algebra.CharP.Frobenius
public import ReasLib.AlgebraicGeometry.Scheme.Characteristic.Prime
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.CategoryTheory.Sites.AbelianSheaf
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived

/-!
# Perfect structure sheaf on the big fppf site

This module defines the additive structure sheaf, its sectionwise Frobenius
endomorphism, and the resulting sequential colimit sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The additive global-functions presheaf on the big fppf site is a sheaf. -/
theorem additiveBigFppfStructurePresheaf_isSheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (Scheme.Over.commStructurePresheaf (Functor.id (Over S)) ⋙
        (forget₂ CommRingCat RingCat.{u + 1} ⋙ forget₂ RingCat AddCommGrpCat.{u + 1})) :=
  sorry

/-- Forget commutative rings to abelian groups through rings. -/
def commRingToAddCommGrp : CommRingCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ CommRingCat RingCat.{u + 1} ⋙ forget₂ RingCat AddCommGrpCat.{u + 1}

/-- The additive sheaf underlying the commutative structure sheaf on the big fppf site. -/
def additiveBigFppfStructureSheaf (S : Scheme.{u}) :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} where
  obj := Scheme.Over.commStructurePresheaf (Functor.id (Over S)) ⋙ commRingToAddCommGrp
  property := additiveBigFppfStructurePresheaf_isSheaf S

/-- The underlying presheaf of the additive big fppf structure sheaf. -/
theorem additiveBigFppfStructureSheaf_obj (S : Scheme.{u}) :
    (additiveBigFppfStructureSheaf S).obj =
      Scheme.Over.commStructurePresheaf (Functor.id (Over S)) ⋙ commRingToAddCommGrp :=
  sorry

/-- The prime `p` vanishes in every lifted global-sections ring of a scheme of characteristic `p`. -/
theorem commStructurePresheaf_prime_cast_eq_zero
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] (U : (Over S)ᵒᵖ) :
    (p : (Scheme.Over.commStructurePresheaf (Functor.id (Over S))).obj U) = 0 :=
  sorry

/-- Section restriction commutes with the sectionwise Frobenius endomorphism. -/
theorem structureSheafFrobeniusRing_naturality
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (Scheme.Over.commStructurePresheaf (Functor.id (Over S))).map f ≫
        CommRingCat.ofHom
          (RingHom.frobeniusOfPrime p (commStructurePresheaf_prime_cast_eq_zero p S V)) =
      CommRingCat.ofHom
          (RingHom.frobeniusOfPrime p (commStructurePresheaf_prime_cast_eq_zero p S U)) ≫
        (Scheme.Over.commStructurePresheaf (Functor.id (Over S))).map f :=
  sorry

/-- The sectionwise Frobenius endomorphism of the lifted commutative structure presheaf. -/
def structureSheafFrobeniusRing
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] :
    Scheme.Over.commStructurePresheaf (Functor.id (Over S)) ⟶
      Scheme.Over.commStructurePresheaf (Functor.id (Over S)) where
  app U :=
    CommRingCat.ofHom
      (RingHom.frobeniusOfPrime p (commStructurePresheaf_prime_cast_eq_zero p S U))
  naturality := fun {_ _} f => structureSheafFrobeniusRing_naturality p S f

/-- The additive sheaf endomorphism induced by sectionwise `p`-th powers. -/
def structureSheafFrobenius
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] :
    additiveBigFppfStructureSheaf S ⟶ additiveBigFppfStructureSheaf S where
  hom := Functor.whiskerRight (structureSheafFrobeniusRing p S) commRingToAddCommGrp

/-- On sections, the Frobenius endomorphism is the `p`-th power map. -/
theorem structureSheafFrobenius_app
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] (U : (Over S)ᵒᵖ)
    (x : (Scheme.Over.commStructurePresheaf (Functor.id (Over S))).obj U) :
    commRingToAddCommGrp.map ((structureSheafFrobeniusRing p S).app U) x = x ^ p :=
  sorry

/-- The sequential diagram of the additive big fppf structure sheaf under Frobenius. -/
def structureSheafFrobeniusIterate
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] :
    ℕ ⥤ Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  Functor.ofSequence (fun _ : ℕ ↦ structureSheafFrobenius p S)

/-- Every object of the Frobenius diagram is the additive big fppf structure sheaf. -/
theorem structureSheafFrobeniusIterate_obj
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] (n : ℕ) :
    (structureSheafFrobeniusIterate p S).obj n = additiveBigFppfStructureSheaf S :=
  sorry

/-- Every successor arrow of the Frobenius diagram is the Frobenius endomorphism. -/
theorem structureSheafFrobeniusIterate_map_succ
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] (n : ℕ) :
    (structureSheafFrobeniusIterate p S).map (homOfLE n.le_succ) =
      structureSheafFrobenius p S :=
  sorry

/-- The perfect structure sheaf is the sheaf colimit of the Frobenius diagram. -/
def perfStructureSheaf (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}] :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
    (colimit
      (structureSheafFrobeniusIterate p S ⋙
        sheafToPresheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}))

/-- The canonical map from a Frobenius stage to the perfect structure sheaf. -/
def perfStructureSheaf_ι (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}] (n : ℕ) :
    additiveBigFppfStructureSheaf S ⟶ perfStructureSheaf p S :=
  (Sheaf.sheafifyCocone
      (colimit.cocone
        (structureSheafFrobeniusIterate p S ⋙
          sheafToPresheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}))).ι.app n

/-- The canonical stage maps satisfy the Frobenius colimit relation. -/
theorem perfStructureSheaf_ι_map
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}] (n : ℕ) :
    structureSheafFrobenius p S ≫ perfStructureSheaf_ι p S (n + 1) =
      perfStructureSheaf_ι p S n :=
  sorry

end AlgebraicGeometry.Scheme

end

end
