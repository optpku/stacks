/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import Mathlib.CategoryTheory.CommSq

/-!
# Base change for presheaves of relative differentials

A commutative square of commutative-ring-valued presheaves induces a natural
map on the sectionwise Kähler-differential presheaves.  This is the common
owner used by sheafification and by sheaf-level base change.
-/

@[expose] public section

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u v

namespace PresheafOfModules.RelativeDifferentials

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ O₁' O₂' : Cᵒᵖ ⥤ CommRingCat.{max u v}}
variable {a : O₁ ⟶ O₁'} {phi : O₁ ⟶ O₂}
variable {phi' : O₁' ⟶ O₂'} {b : O₂ ⟶ O₂'}

/-- Restriction of module presheaves along the lower edge of a square of
commutative-ring presheaves. -/
abbrev restriction (b : O₂ ⟶ O₂') :=
  PresheafOfModules.restrictScalars
    (PresheafOfModules.presheafStructureMap b)

/-- A commutative presheaf square is commutative on every section ring. -/
theorem squareApp (sq : CommSq a phi phi' b) (X : Cᵒᵖ) :
    a.app X ≫ phi'.app X = phi.app X ≫ b.app X := sorry

/-- The sectionwise Kähler-differential map induced by a commutative
presheaf square. -/
abbrev mapApp (sq : CommSq a phi phi' b) (X : Cᵒᵖ) :
    (relativeDifferentials' phi).obj X ⟶
      ((restriction b).obj (relativeDifferentials' phi')).obj X :=
  CommRingCat.KaehlerDifferential.map (squareApp sq X)

/-- The sectionwise maps on Kähler differentials commute with restriction
morphisms of the indexing category. -/
theorem mapApp_naturality (sq : CommSq a phi phi' b)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (relativeDifferentials' phi).map f ≫
        (ModuleCat.restrictScalars (((ringPresheaf O₂).map f).hom)).map
          (mapApp sq Y) =
      mapApp sq X ≫
        ((restriction b).obj (relativeDifferentials' phi')).map f := sorry

/-- The natural morphism on presheaves of relative differentials induced by a
commutative square of commutative-ring presheaves. -/
noncomputable def map (sq : CommSq a phi phi' b) :
    relativeDifferentials' phi ⟶
      (restriction b).obj (relativeDifferentials' phi') where
  app X := mapApp sq X
  naturality f := mapApp_naturality sq f

end PresheafOfModules.RelativeDifferentials
