/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Absolute

/-!
# Frobenius colimits of structure sheaves

This module defines the sequential colimit of a scheme's structure sheaf under
sectionwise Frobenius, together with its canonical cocone and universal property.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.FrobeniusColimit

/-- The sectionwise Frobenius endomorphism of the underlying sheaf of rings. -/
def ringSheafMap (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] :
    S.ringCatSheaf ⟶ S.ringCatSheaf where
  hom := Functor.whiskerRight (Scheme.absoluteFrobeniusNatTrans p S)
    (forget₂ CommRingCat RingCat.{u})

/-- The Frobenius sheaf endomorphism sends a section to its `p`-th power. -/
theorem ringSheafMap_app (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    (U : S.Opens) (s : S.presheaf.obj (.op U)) :
    RingCat.Hom.hom ((ringSheafMap p S).hom.app (.op U)) s = s ^ p := sorry

/-- The sequential diagram of structure sheaves under sectionwise Frobenius. -/
def ringSheafDiagram (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] :
    ℕ ⥤ TopCat.Sheaf RingCat.{u} S :=
  Functor.ofSequence (fun _ : ℕ ↦ ringSheafMap p S)

/-- Every object of the structure-sheaf Frobenius diagram is the structure sheaf of `S`. -/
theorem ringSheafDiagram_obj (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    (n : ℕ) :
    (ringSheafDiagram p S).obj n = S.ringCatSheaf := sorry

/-- Every successor map in the structure-sheaf diagram is Frobenius. -/
theorem ringSheafDiagram_map_succ (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.IsCharP p] (n : ℕ) :
    (ringSheafDiagram p S).map (homOfLE n.le_succ) = ringSheafMap p S := sorry

/-- The sequential colimit of the structure sheaf under Frobenius. -/
noncomputable def ringSheaf (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] :
    TopCat.Sheaf RingCat.{u} S :=
  (presheafToSheaf (Opens.grothendieckTopology S) RingCat.{u}).obj
    (colimit (ringSheafDiagram p S ⋙
      sheafToPresheaf (Opens.grothendieckTopology S) RingCat.{u}))

/-- The map from the `n`-th structure-sheaf stage to its Frobenius colimit. -/
noncomputable def toRingSheaf (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    (n : ℕ) : S.ringCatSheaf ⟶ ringSheaf p S :=
  (Sheaf.sheafifyCocone
    (colimit.cocone (ringSheafDiagram p S ⋙
      sheafToPresheaf (Opens.grothendieckTopology S) RingCat.{u}))).ι.app n

/-- The structure-sheaf stage maps are compatible with Frobenius. -/
theorem toRingSheaf_succ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    (n : ℕ) :
    ringSheafMap p S ≫ toRingSheaf p S (n + 1) = toRingSheaf p S n := sorry

/-- The structure-sheaf stage maps form a natural transformation to the constant colimit
diagram. -/
theorem toRingSheaf_naturality (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    {i j : ℕ} (f : i ⟶ j) :
    (ringSheafDiagram p S).map f ≫ toRingSheaf p S j =
      toRingSheaf p S i ≫ ((Functor.const ℕ).obj (ringSheaf p S)).map f := sorry

/-- The canonical cocone from the Frobenius diagram to `ringSheaf p S`. -/
noncomputable def ringSheafCocone (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] :
    Cocone (ringSheafDiagram p S) :=
  Sheaf.sheafifyCocone
    (colimit.cocone (ringSheafDiagram p S ⋙
      sheafToPresheaf (Opens.grothendieckTopology S) RingCat.{u}))

/-- The morphism from the Frobenius-colimit sheaf to another cocone point. -/
noncomputable def ringSheafDesc (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    (c : Cocone (ringSheafDiagram p S)) : ringSheaf p S ⟶ c.pt :=
  (Sheaf.isColimitSheafifyCocone
    (colimit.cocone (ringSheafDiagram p S ⋙
      sheafToPresheaf (Opens.grothendieckTopology S) RingCat.{u}))
    (colimit.isColimit (ringSheafDiagram p S ⋙
      sheafToPresheaf (Opens.grothendieckTopology S) RingCat.{u}))).desc c

/-- The colimit descent morphism agrees with every leg of the given cocone. -/
theorem ringSheafDesc_fac (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    (c : Cocone (ringSheafDiagram p S)) (n : ℕ) :
    toRingSheaf p S n ≫ ringSheafDesc p S c = c.ι.app n := sorry

/-- The colimit descent morphism is uniquely determined by its values on all stages. -/
theorem ringSheafDesc_uniq (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    (c : Cocone (ringSheafDiagram p S)) (f : ringSheaf p S ⟶ c.pt)
    (hf : ∀ n, toRingSheaf p S n ≫ f = c.ι.app n) :
    f = ringSheafDesc p S c := sorry

/-- The canonical Frobenius cocone exhibits `ringSheaf p S` as the sheaf colimit. -/
noncomputable def ringSheafCoconeIsColimit (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.IsCharP p] :
    IsColimit (ringSheafCocone p S) :=
  Sheaf.isColimitSheafifyCocone
    (colimit.cocone (ringSheafDiagram p S ⋙
      sheafToPresheaf (Opens.grothendieckTopology S) RingCat.{u}))
    (colimit.isColimit (ringSheafDiagram p S ⋙
      sheafToPresheaf (Opens.grothendieckTopology S) RingCat.{u}))

end AlgebraicGeometry.Scheme.FrobeniusColimit
