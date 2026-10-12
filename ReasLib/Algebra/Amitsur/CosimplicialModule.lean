/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import ReasLib.Algebra.Category.CommAlgCat.Module
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import ReasLib.AlgebraicTopology.Cech.Conerve.Coprojection

/-!
# Modules over the Amitsur cosimplicial ring

This file defines the Amitsur cosimplicial algebra and modules over its
degreewise rings, together with their basic evaluation and structure-map API.
-/

@[expose] public section

noncomputable section

open CategoryTheory ModuleCat Opposite

universe u

namespace Algebra.Amitsur

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The Amitsur cosimplicial algebra of `R → A`, presented as the Čech conerve. -/
abbrev cosimplicialAlgebra : CosimplicialObject (CommAlgCat.{u} R) :=
  (Arrow.mk (CommAlgCat.ofHom (Algebra.ofId R A))).cechConerve

/-- The commutative-ring-valued diagram underlying the Amitsur cosimplicial algebra. -/
abbrev cosimplicialCommRing : SimplexCategory ⥤ CommRingCat.{u} :=
  cosimplicialAlgebra R A ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u}

/-- The ring-valued diagram underlying the Amitsur cosimplicial algebra. -/
abbrev cosimplicialRing : SimplexCategory ⥤ RingCat.{u} :=
  cosimplicialCommRing R A ⋙ forget₂ CommRingCat.{u} RingCat.{u}

/-- Modules over the varying rings of the Amitsur cosimplicial ring. -/
abbrev CosimplicialModule :=
  PresheafOfModules.{u} (unopUnop SimplexCategory ⋙ cosimplicialRing R A)

namespace CosimplicialModule

/-- Evaluate an Amitsur cosimplicial module in a simplex degree. -/
abbrev eval (M : CosimplicialModule R A) (Δ : SimplexCategory) :
    ModuleCat.{u} ((cosimplicialRing R A).obj Δ) :=
  M.obj (op (op Δ))

/-- The structure map of an Amitsur cosimplicial module along a simplex morphism. -/
abbrev map (M : CosimplicialModule R A) {Δ Γ : SimplexCategory} (β : Δ ⟶ Γ) :
    eval R A M Δ ⟶
      (ModuleCat.restrictScalars ((cosimplicialRing R A).map β).hom).obj
        (eval R A M Γ) :=
  PresheafOfModules.map M β.op.op

/-- The component of a morphism of Amitsur cosimplicial modules in a simplex degree. -/
abbrev app {M M' : CosimplicialModule R A} (f : M ⟶ M')
    (Δ : SimplexCategory) : eval R A M Δ ⟶ eval R A M' Δ :=
  PresheafOfModules.Hom.app f (op (op Δ))

/-- Forget the varying scalar rings of an Amitsur cosimplicial module. -/
noncomputable def underlying (M : CosimplicialModule R A) : CosimplicialObject Ab :=
  opOp SimplexCategory ⋙ M.presheaf

end CosimplicialModule

/-- The vertex homomorphism from `A` into one degree of the Amitsur cosimplicial ring. -/
noncomputable def vertex (Δ : SimplexCategory) (i : Fin (Δ.len + 1)) :
    A →+* (cosimplicialCommRing R A).obj Δ :=
  (Arrow.cechConerve.ι
    (Arrow.mk (CommAlgCat.ofHom (Algebra.ofId R A))) Δ i).hom.toRingHom

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Every vertex of the Amitsur cosimplicial algebra lies over the structural map from `R`. -/
theorem vertex_overBase (Δ : SimplexCategory) (i : Fin (Δ.len + 1)) :
    (CommRingCat.ofHom (vertex R A Δ i)).op ≫
        (CommRingCat.ofHom (Algebra.ofId R A)).op =
      (CommRingCat.ofHom
        (algebraMap R ((cosimplicialAlgebra R A).obj Δ))).op := sorry

/-- The ring map of a simplex morphism carries each source vertex to its reindexed target
vertex. -/
theorem vertex_map {Δ Γ : SimplexCategory} (β : Δ ⟶ Γ)
    (i : Fin (Δ.len + 1)) :
    vertex R A Γ (β.toOrderHom i) =
      ((cosimplicialCommRing R A).map β).hom.comp
        (vertex R A Δ i) := sorry

end Algebra.Amitsur
