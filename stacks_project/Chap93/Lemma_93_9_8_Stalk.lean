/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import stacks_project.Chap93.Lemma_93_9_7_Algebras
public import stacks_project.Chap93.Example_93_9_1_Schemes_Deformation

/-!
# Stalk functor of scheme deformations

A point `p` of a scheme `X` over `k` induces a functor of deformation
categories sending a deformation `(A, Y)` of `X` to the stalk pair
`(A, Y.scheme.presheaf.stalk (schemeHom p))` over `X.presheaf.stalk p`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped BasedFunctor

noncomputable section

universe u

namespace FlatSchemeCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The Artinian base of a pair `(A, Y)` acts on the structure-sheaf stalk at
any point of `Y` via `ΓSpecIso.inv ≫ structureHom.appTop ≫ germ`. -/
instance instAlgebra_structureStalk (Y : FlatSchemeCat Λ k) (y : Y.scheme) :
    Algebra Y.base.carrier (Y.scheme.presheaf.stalk y : Type u) :=
  ((Scheme.ΓSpecIso (CommRingCat.of Y.base.carrier)).inv ≫
      Y.structureHom.appTop ≫ Y.scheme.presheaf.germ ⊤ y trivial).hom.toAlgebra

variable (X : Scheme.{u})
  (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
  (p : X)

/-- The `k`-algebra structure on the stalk `X.presheaf.stalk p` induced by the
structure morphism of `X` over `k`. This is not an `instance` because the acting
map depends on the explicit morphism `hX`, which typeclass search cannot recover
from the stalk type. -/
abbrev algebra_presheafStalk :
    Algebra k (X.presheaf.stalk p : Type u) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)).inv ≫
      hX.appTop ≫ X.presheaf.germ ⊤ p trivial).hom.toAlgebra

/-- The residue pair `(k, O_{X, p})` of Example 93.8.1, with the `k`-algebra
structure supplied by `algebra_presheafStalk`. -/
def residueStalk : FlatAlgebraCat Λ k where
  base := ArtinianLocalAlgCat.residue Λ k
  algebra := (X.presheaf.stalk p : Type u)
  isAlgebra := algebra_presheafStalk X hX p
  isFlat := sorry

/-- `residueStalk` is based on the residue object of `C_Λ`. -/
theorem residueStalk_base :
    (residueStalk X hX p).base = ArtinianLocalAlgCat.residue Λ k :=
  sorry

/-- The algebra of `residueStalk` is the structure-sheaf stalk at `p`. -/
theorem residueStalk_algebra :
    (residueStalk X hX p).algebra = (X.presheaf.stalk p : Type u) :=
  sorry

/-- `residueStalk` as an object of the residue fibre of `FlatAlgebraCat.forget`. -/
def residueStalkObj :
    FlatAlgebraCat.forget.Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  Fiber.mk
    (rfl : FlatAlgebraCat.forget.obj (residueStalk X hX p) =
      ArtinianLocalAlgCat.residue Λ k)

/-- The deformation category `Def_{O_{X, p}}` of the stalk, as in Example 93.8.1. -/
abbrev stalkDeformationCategory :=
  Over (Fiber.fiberInclusion.obj (residueStalkObj X hX p))

/-- `stalkDeformationCategory` is the Over-slice of the residue pair `(k, O_{X, p})`. -/
theorem stalkDeformationCategory_spec :
    stalkDeformationCategory X hX p =
      Over (Fiber.fiberInclusion.obj (residueStalkObj X hX p)) :=
  sorry

variable [AlgebraicGeometry.Flat hX]

/-- The pair `(A, O_{Y, schemeHom p})` attached to a deformation `(A, Y)` of `X`. -/
def stalkObj (ξ : deformationCategory Λ k X hX) : FlatAlgebraCat Λ k where
  base := ξ.left.base
  algebra := (ξ.left.scheme.presheaf.stalk (ξ.hom.schemeHom p) : Type u)
  isAlgebra := instAlgebra_structureStalk ξ.left (ξ.hom.schemeHom p)
  isFlat := sorry

/-- `stalkObj` keeps the Artinian local base of the original deformation. -/
theorem stalkObj_base (ξ : deformationCategory Λ k X hX) :
    (stalkObj X hX p ξ).base = ξ.left.base :=
  sorry

/-- The algebra of `stalkObj` is the structure-sheaf stalk at the preimage of `p`. -/
theorem stalkObj_algebra (ξ : deformationCategory Λ k X hX) :
    (stalkObj X hX p ξ).algebra =
      (ξ.left.scheme.presheaf.stalk (ξ.hom.schemeHom p) : Type u) :=
  sorry

/-- The residue arrow `(A, O_{Y, schemeHom p}) ⟶ (k, O_{X, p})` induced by
`schemeHom.stalkMap` at `p`. -/
def stalkResidueHom (ξ : deformationCategory Λ k X hX) :
    stalkObj X hX p ξ ⟶ residueStalk X hX p where
  baseHom := ξ.hom.baseHom
  toRingHom := (ξ.hom.schemeHom.stalkMap p).hom
  commutes := sorry
  isIso_tensor := sorry

/-- `stalkResidueHom` keeps the underlying morphism of Artinian local algebras. -/
theorem stalkResidueHom_baseHom (ξ : deformationCategory Λ k X hX) :
    (stalkResidueHom X hX p ξ).baseHom = ξ.hom.baseHom :=
  sorry

/-- A morphism of deformations of `X` induces the corresponding stalk map of
structure sheaves at the preimage of `p`. -/
def stalkObjHom {ξ η : deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    stalkObj X hX p ξ ⟶ stalkObj X hX p η where
  baseHom := φ.left.baseHom
  toRingHom :=
    (eqToHom
          (congrArg (fun x ↦ ξ.left.scheme.presheaf.stalk x)
            (congrArg (fun h ↦ h.schemeHom p) (Over.w φ)).symm) ≫
        φ.left.schemeHom.stalkMap (η.hom.schemeHom p)).hom
  commutes := sorry
  isIso_tensor := sorry

/-- `stalkObjHom` keeps the underlying morphism of Artinian local algebras. -/
theorem stalkObjHom_baseHom {ξ η : deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    (stalkObjHom X hX p φ).baseHom = φ.left.baseHom :=
  sorry

variable (Λ k) in
/-- The functor `Def_X ⥤ Def_{O_{X, p}}` sending a deformation `(A, Y)` of `X`
to the stalk pair `(A, O_{Y, schemeHom p})` over `O_{X, p}`. -/
def stalkFunctor :
    deformationCategory Λ k X hX ⥤ stalkDeformationCategory X hX p where
  obj ξ := Over.mk (stalkResidueHom X hX p ξ)
  map φ := Over.homMk (stalkObjHom X hX p φ) sorry
  map_id := sorry
  map_comp := sorry

/-- Objects of `stalkFunctor` are the stalk residue arrows `stalkResidueHom`. -/
theorem stalkFunctor_obj (ξ : deformationCategory Λ k X hX) :
    (stalkFunctor Λ k X hX p).obj ξ = Over.mk (stalkResidueHom X hX p ξ) :=
  sorry

/-- An object of `Def_X` and its stalk image have the same Artinian base. -/
theorem stalkFunctor_obj_left_base (ξ : deformationCategory Λ k X hX) :
    ((stalkFunctor Λ k X hX p).obj ξ).left.base = ξ.left.base :=
  sorry

/-- The algebra of a `stalkFunctor` image is the structure-sheaf stalk at the
preimage of `p`. -/
theorem stalkFunctor_obj_algebra (ξ : deformationCategory Λ k X hX) :
    ((stalkFunctor Λ k X hX p).obj ξ).left.algebra =
      (ξ.left.scheme.presheaf.stalk (ξ.hom.schemeHom p) : Type u) :=
  sorry

/-- `stalkFunctor` lies strictly over `ArtinianLocalAlgCat`. -/
theorem stalkFunctor_comp_forget :
    stalkFunctor Λ k X hX p ⋙
        Over.forget (Fiber.fiberInclusion.obj (residueStalkObj X hX p)) ⋙
          FlatAlgebraCat.forget =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k :=
  sorry

variable (Λ k) in
/-- The stalk functor as a morphism of categories over `C_Λ`. -/
def stalkBasedFunctor :
    BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k) ⥤ᵇ
      BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (residueStalkObj X hX p)) ⋙
          FlatAlgebraCat.forget) :=
  BasedFunctor.ofFunctor (stalkFunctor Λ k X hX p) (stalkFunctor_comp_forget X hX p)

/-- The underlying ordinary functor of `stalkBasedFunctor` is `stalkFunctor`. -/
theorem stalkBasedFunctor_toFunctor :
    (stalkBasedFunctor Λ k X hX p).toFunctor = stalkFunctor Λ k X hX p :=
  sorry

end FlatSchemeCat

end
