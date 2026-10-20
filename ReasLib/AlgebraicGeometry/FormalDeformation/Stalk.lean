/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra
public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReasLib.RingTheory.Henselian.Pair.Completion
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.AdicCompletion

/-!
# Stalk functor of scheme deformations

A point `p` of a scheme `X` over `k` induces a functor of deformation
categories sending a deformation `(A, Y)` of `X` to the stalk pair
`(A, Y.scheme.presheaf.stalk (schemeHom p))` over `X.presheaf.stalk p`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing RingPairCat
open scoped BasedFunctor

noncomputable section

universe u

namespace FlatSchemeCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The Artinian base of a pair `(A, Y)` acts on the structure-sheaf stalk at
any point of `Y` via `ΓSpecIso.inv ≫ structureHom.appTop ≫ germ`. -/
@[reducible] def instAlgebra_structureStalk (Y : FlatSchemeCat Λ k) (y : Y.scheme) :
    Algebra Y.base.carrier (Y.scheme.presheaf.stalk y : Type u) :=
  ((Scheme.ΓSpecIso (CommRingCat.of Y.base.carrier)).inv ≫
      Y.structureHom.appTop ≫ Y.scheme.presheaf.germ ⊤ y trivial).hom.toAlgebra

variable (X : Scheme.{u})
  (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
  (p : X)

/-- The structure morphism to the residue field induces a `k`-algebra structure
on the structure-sheaf stalk at `p`. -/
abbrev algebra_presheafStalk :
    Algebra k (X.presheaf.stalk p : Type u) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)).inv ≫
      hX.appTop ≫ X.presheaf.germ ⊤ p trivial).hom.toAlgebra

/-- The structure-sheaf stalk is flat over the residue field acting through the structure morphism. -/
theorem residueStalk_flat :
    @Module.Flat (ArtinianLocalAlgCat.residue Λ k).carrier
      (X.presheaf.stalk p : Type u) _ _
      (@Algebra.toModule _ _ _ _ (algebra_presheafStalk X hX p)) :=
  sorry

/-- The flat residue pair consists of the residue field and the structure-sheaf stalk. -/
def residueStalk : FlatAlgebraCat Λ k :=
  FlatAlgebraCat.of (ArtinianLocalAlgCat.residue Λ k)
    (X.presheaf.stalk p : Type u)
    (isAlgebra := algebra_presheafStalk X hX p)
    (isFlat := residueStalk_flat X hX p)

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

/-- The deformation category of a stalk is the slice over its residue pair. -/
abbrev stalkDeformationCategory :=
  Over (Fiber.fiberInclusion.obj (residueStalkObj X hX p))

/-- `stalkDeformationCategory` is the Over-slice of the residue pair `(k, O_{X, p})`. -/
theorem stalkDeformationCategory_spec :
    stalkDeformationCategory X hX p =
      Over (Fiber.fiberInclusion.obj (residueStalkObj X hX p)) :=
  sorry

variable [AlgebraicGeometry.Flat hX]

/-- The structure-sheaf stalk of a flat deformation is flat over its stored base. -/
theorem stalkObj_flat (ξ : deformationCategory Λ k X hX) :
    @Module.Flat ξ.left.base.carrier
      (ξ.left.scheme.presheaf.stalk (ξ.hom.schemeHom p) : Type u) _ _
      (@Algebra.toModule _ _ _ _
        (instAlgebra_structureStalk ξ.left (ξ.hom.schemeHom p))) :=
  sorry

/-- The pair `(A, O_{Y, schemeHom p})` attached to a deformation. -/
def stalkObj (ξ : deformationCategory Λ k X hX) : FlatAlgebraCat Λ k :=
  FlatAlgebraCat.of ξ.left.base
    (ξ.left.scheme.presheaf.stalk (ξ.hom.schemeHom p) : Type u)
    (isAlgebra := instAlgebra_structureStalk ξ.left (ξ.hom.schemeHom p))
    (isFlat := stalkObj_flat X hX p ξ)

/-- `stalkObj` keeps the Artinian local base of the original deformation. -/
theorem stalkObj_base (ξ : deformationCategory Λ k X hX) :
    (stalkObj X hX p ξ).base = ξ.left.base :=
  sorry

/-- The algebra of `stalkObj` is the structure-sheaf stalk at the preimage of `p`. -/
theorem stalkObj_algebra (ξ : deformationCategory Λ k X hX) :
    (stalkObj X hX p ξ).algebra =
      (ξ.left.scheme.presheaf.stalk (ξ.hom.schemeHom p) : Type u) :=
  sorry

/-- The special-fibre stalk map commutes with the scalar maps of the deformation. -/
theorem stalkResidueHom_commutes (ξ : deformationCategory Λ k X hX) :
    (ξ.hom.schemeHom.stalkMap p).hom.comp
        (algebraMap (stalkObj X hX p ξ).base.carrier (stalkObj X hX p ξ).algebra) =
      (algebraMap (residueStalk X hX p).base.carrier (residueStalk X hX p).algebra).comp
        ξ.hom.baseHom.hom.toRingHom :=
  sorry

/-- The canonical tensor lift of the special-fibre stalk map is bijective. -/
theorem stalkResidueHom_isIso_tensor (ξ : deformationCategory Λ k X hX) :
    Function.Bijective (FlatAlgebraCat.canonicalTensorMap
      (Q := stalkObj X hX p ξ) (P := residueStalk X hX p)
      ξ.hom.baseHom (ξ.hom.schemeHom.stalkMap p).hom
      (stalkResidueHom_commutes X hX p ξ)) :=
  sorry

/-- The residue arrow `(A, O_{Y, schemeHom p}) ⟶ (k, O_{X, p})` induced by
`schemeHom.stalkMap` at `p`. -/
def stalkResidueHom (ξ : deformationCategory Λ k X hX) :
    stalkObj X hX p ξ ⟶ residueStalk X hX p :=
  FlatAlgebraCat.Hom.of ξ.hom.baseHom (ξ.hom.schemeHom.stalkMap p).hom
    (stalkResidueHom_commutes X hX p ξ)
    (stalkResidueHom_isIso_tensor X hX p ξ)

/-- `stalkResidueHom` keeps the underlying morphism of Artinian local algebras. -/
theorem stalkResidueHom_baseHom (ξ : deformationCategory Λ k X hX) :
    (stalkResidueHom X hX p ξ).baseHom = ξ.hom.baseHom :=
  sorry

/-- The transported stalk map of a deformation arrow commutes with its base map. -/
theorem stalkObjHom_commutes {ξ η : deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    (eqToHom
          (congrArg (fun x ↦ ξ.left.scheme.presheaf.stalk x)
            (congrArg (fun h ↦ h.schemeHom p) (Over.w φ)).symm) ≫
        φ.left.schemeHom.stalkMap (η.hom.schemeHom p)).hom.comp
        (algebraMap (stalkObj X hX p ξ).base.carrier (stalkObj X hX p ξ).algebra) =
      (algebraMap (stalkObj X hX p η).base.carrier (stalkObj X hX p η).algebra).comp
        φ.left.baseHom.hom.toRingHom :=
  sorry

/-- The canonical tensor lift of the transported stalk map is bijective. -/
theorem stalkObjHom_isIso_tensor {ξ η : deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    Function.Bijective (FlatAlgebraCat.canonicalTensorMap
      (Q := stalkObj X hX p ξ) (P := stalkObj X hX p η) φ.left.baseHom
      (eqToHom
          (congrArg (fun x ↦ ξ.left.scheme.presheaf.stalk x)
            (congrArg (fun h ↦ h.schemeHom p) (Over.w φ)).symm) ≫
        φ.left.schemeHom.stalkMap (η.hom.schemeHom p)).hom
      (stalkObjHom_commutes X hX p φ)) :=
  sorry

/-- A morphism of deformations of `X` induces the corresponding stalk map of
structure sheaves at the preimage of `p`. -/
def stalkObjHom {ξ η : deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    stalkObj X hX p ξ ⟶ stalkObj X hX p η :=
  FlatAlgebraCat.Hom.of φ.left.baseHom
    (eqToHom
          (congrArg (fun x ↦ ξ.left.scheme.presheaf.stalk x)
            (congrArg (fun h ↦ h.schemeHom p) (Over.w φ)).symm) ≫
        φ.left.schemeHom.stalkMap (η.hom.schemeHom p)).hom
    (stalkObjHom_commutes X hX p φ)
    (stalkObjHom_isIso_tensor X hX p φ)

/-- `stalkObjHom` keeps the underlying morphism of Artinian local algebras. -/
theorem stalkObjHom_baseHom {ξ η : deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    (stalkObjHom X hX p φ).baseHom = φ.left.baseHom :=
  sorry

/-- Stalk maps of deformation arrows commute with the residue stalk arrows. -/
theorem stalkResidueHom_naturality {ξ η : deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    stalkObjHom X hX p φ ≫ stalkResidueHom X hX p η = stalkResidueHom X hX p ξ :=
  sorry

/-- Taking stalks preserves the identity deformation arrow. -/
theorem stalkObjHom_id (ξ : deformationCategory Λ k X hX) :
    stalkObjHom X hX p (𝟙 ξ) = 𝟙 (stalkObj X hX p ξ) :=
  sorry

/-- Taking stalks preserves composition of deformation arrows. -/
theorem stalkObjHom_comp {ξ η ζ : deformationCategory Λ k X hX}
    (φ : ξ ⟶ η) (ψ : η ⟶ ζ) :
    stalkObjHom X hX p (φ ≫ ψ) = stalkObjHom X hX p φ ≫ stalkObjHom X hX p ψ :=
  sorry

variable (Λ k) in
/-- The functor `Def_X ⥤ Def_{O_{X, p}}` sending a deformation `(A, Y)` of `X`
to the stalk pair `(A, O_{Y, schemeHom p})` over `O_{X, p}`. -/
def stalkFunctor :
    deformationCategory Λ k X hX ⥤ stalkDeformationCategory X hX p where
  obj ξ := Over.mk (stalkResidueHom X hX p ξ)
  map φ := Over.homMk (stalkObjHom X hX p φ) (stalkResidueHom_naturality X hX p φ)
  map_id ξ := by
    apply Over.OverMorphism.ext
    exact stalkObjHom_id X hX p ξ
  map_comp φ ψ := by
    apply Over.OverMorphism.ext
    exact stalkObjHom_comp X hX p φ ψ

/-- Objects of `stalkFunctor` are the stalk residue arrows `stalkResidueHom`. -/
theorem stalkFunctor_obj (ξ : deformationCategory Λ k X hX) :
    (stalkFunctor Λ k X hX p).obj ξ = Over.mk (stalkResidueHom X hX p ξ) :=
  sorry

/-- The underlying flat algebra of a stalk-functor image is the stalk pair of the deformation. -/
theorem stalkFunctor_obj_left (ξ : deformationCategory Λ k X hX) :
    ((stalkFunctor Λ k X hX p).obj ξ).left = stalkObj X hX p ξ :=
  rfl

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

namespace FlatSchemeCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : Scheme.{u})
  (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
variable (p : X)

/-- The structure-sheaf stalk with its algebra structure determined by the structure morphism. -/
def structureStalk : Type u :=
  (fun _ ↦ (X.presheaf.stalk p : Type u)) hX

/-- `structureStalk` is the structure-sheaf stalk at `p`. -/
theorem structureStalk_eq : structureStalk X hX p = X.presheaf.stalk p :=
  rfl

/-- The commutative ring structure on `O_{X, p}`. -/
instance instCommRing_structureStalk : CommRing (structureStalk X hX p) :=
  inferInstanceAs (CommRing (X.presheaf.stalk p))

/-- The structure-sheaf stalk is a local ring. -/
instance instIsLocalRing_structureStalk : IsLocalRing (structureStalk X hX p) :=
  inferInstanceAs (IsLocalRing (X.presheaf.stalk p))

/-- The `k`-algebra structure on `O_{X, p}` induced by the structure morphism
`hX`. -/
instance instAlgebra_k_structureStalk : Algebra k (structureStalk X hX p) :=
  algebra_presheafStalk X hX p

/-- Scalar multiplication of `k` on `O_{X, p}` is the germ of the structure
morphism of `X` over `k`. -/
theorem algebraMap_structureStalk (x : k) :
    algebraMap k (structureStalk X hX p) x =
      ((Scheme.ΓSpecIso (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)).inv ≫
          hX.appTop ≫ X.presheaf.germ ⊤ p trivial).hom x :=
  rfl

/-- On a locally Noetherian scheme, the structure-sheaf stalk is Noetherian. -/
instance instIsNoetherianRing_structureStalk [IsLocallyNoetherian X] :
    IsNoetherianRing (structureStalk X hX p) :=
  inferInstanceAs (IsNoetherianRing (X.presheaf.stalk p))

/-- The completion `O_{X, p}^∧` of the local ring at `p`. -/
abbrev completeStalk : Type u :=
  AdicCompletion (maximalIdeal (structureStalk X hX p)) (structureStalk X hX p)

/-- `completeStalk` is the adic completion of `O_{X, p}` along its maximal ideal. -/
theorem completeStalk_eq :
    completeStalk X hX p =
      AdicCompletion (maximalIdeal (structureStalk X hX p)) (structureStalk X hX p) :=
  rfl

/-- Scalar multiplication of `k` on `O_{X, p}^∧` factors through `O_{X, p}`. -/
theorem algebraMap_completeStalk (x : k) :
    algebraMap k (completeStalk X hX p) x =
      algebraMap (structureStalk X hX p) (completeStalk X hX p)
        (algebraMap k (structureStalk X hX p) x) :=
  IsScalarTower.algebraMap_apply k (structureStalk X hX p) (completeStalk X hX p) x

section Henselization

variable [henselianPairInclusion.IsRightAdjoint]

/-- The henselization `O_{X, p}^h` of the local ring at `p`. -/
abbrev henselStalk : Type u :=
  henselizationRing (pairOfIdeal (maximalIdeal (structureStalk X hX p)))

/-- `henselStalk` is the pair henselization of `(O_{X, p}, m_p)`. -/
theorem henselStalk_eq :
    henselStalk X hX p =
      henselizationRing (pairOfIdeal (maximalIdeal (structureStalk X hX p))) :=
  rfl

/-- The `k`-algebra structure on `O_{X, p}^h` via `k → O_{X, p} → O_{X, p}^h`. -/
instance instAlgebra_k_henselStalk : Algebra k (henselStalk X hX p) :=
  (RingHom.comp (toHenselization (pairOfIdeal (maximalIdeal (structureStalk X hX p))))
    (algebraMap k (structureStalk X hX p))).toAlgebra

/-- Scalar multiplication of `k` on `O_{X, p}^h` factors through `O_{X, p}`. -/
theorem algebraMap_henselStalk (x : k) :
    algebraMap k (henselStalk X hX p) x =
      algebraMap (structureStalk X hX p) (henselStalk X hX p)
        (algebraMap k (structureStalk X hX p) x) :=
  rfl

/-- Pair henselization of a Noetherian local stalk remains Noetherian. -/
instance instIsNoetherianRing_henselStalk [IsNoetherianRing (structureStalk X hX p)] :
    IsNoetherianRing (henselStalk X hX p) :=
  @henselizationRing_isNoetherian (pairOfIdeal (maximalIdeal (structureStalk X hX p)))
    (inferInstanceAs (IsNoetherianRing (structureStalk X hX p))) _

end Henselization

variable [AlgebraicGeometry.Flat hX]

/-- The pair `(A, O_{Y, schemeHom p})` attached to a deformation `(A, Y)` of `X`,
as a flat algebra over `A` with residue ring `structureStalk`. -/
def stalkAlgebraObj (ξ : deformationCategory Λ k X hX) : FlatAlgebraCat Λ k :=
  FlatAlgebraCat.of ξ.left.base
    (ξ.left.scheme.presheaf.stalk (ξ.hom.schemeHom p) : Type u)
    (isAlgebra := instAlgebra_structureStalk ξ.left (ξ.hom.schemeHom p))
    (isFlat := stalkObj_flat X hX p ξ)

/-- `stalkAlgebraObj` keeps the Artinian local base of the original deformation. -/
theorem stalkAlgebraObj_base (ξ : deformationCategory Λ k X hX) :
    (stalkAlgebraObj X hX p ξ).base = ξ.left.base :=
  rfl

/-- The residue arrow `(A, O_{Y, schemeHom p}) ⟶ (k, O_{X, p})` induced by
`schemeHom.stalkMap` at `p`, targeting `ofResidue` of `structureStalk`. -/
def stalkAlgebraResidueHom (ξ : deformationCategory Λ k X hX) :
    stalkAlgebraObj X hX p ξ ⟶ FlatAlgebraCat.ofResidue Λ k (structureStalk X hX p) :=
  FlatAlgebraCat.Hom.of ξ.hom.baseHom (ξ.hom.schemeHom.stalkMap p).hom
    (stalkResidueHom_commutes X hX p ξ) (stalkResidueHom_isIso_tensor X hX p ξ)

/-- `stalkAlgebraResidueHom` keeps the underlying morphism of Artinian local
algebras. -/
theorem stalkAlgebraResidueHom_baseHom (ξ : deformationCategory Λ k X hX) :
    (stalkAlgebraResidueHom X hX p ξ).baseHom = ξ.hom.baseHom :=
  rfl

/-- A morphism of deformations of `X` induces the corresponding stalk map of
structure sheaves at the preimage of `p`. -/
def stalkAlgebraObjHom {ξ η : deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    stalkAlgebraObj X hX p ξ ⟶ stalkAlgebraObj X hX p η :=
  FlatAlgebraCat.Hom.of φ.left.baseHom
    (eqToHom
          (congrArg (fun x ↦ ξ.left.scheme.presheaf.stalk x)
            (congrArg (fun h ↦ h.schemeHom p) (Over.w φ)).symm) ≫
        φ.left.schemeHom.stalkMap (η.hom.schemeHom p)).hom
    (stalkObjHom_commutes X hX p φ) (stalkObjHom_isIso_tensor X hX p φ)

/-- `stalkAlgebraObjHom` keeps the underlying morphism of Artinian local algebras. -/
theorem stalkAlgebraObjHom_baseHom {ξ η : deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    (stalkAlgebraObjHom X hX p φ).baseHom = φ.left.baseHom :=
  rfl

variable (Λ k) in
/-- The functor `Def_X ⥤ Def_{O_{X, p}}` sending a deformation `(A, Y)` of `X`
to the stalk pair `(A, O_{Y, schemeHom p})` over `structureStalk`. -/
def stalkAlgebraFunctor :
    deformationCategory Λ k X hX ⥤
      FlatAlgebraCat.deformationCategory Λ k (structureStalk X hX p) where
  obj ξ := Over.mk (stalkAlgebraResidueHom X hX p ξ)
  map φ := Over.homMk (stalkAlgebraObjHom X hX p φ) (stalkResidueHom_naturality X hX p φ)
  map_id ξ := by
    apply Over.OverMorphism.ext
    exact stalkObjHom_id X hX p ξ
  map_comp φ ψ := by
    apply Over.OverMorphism.ext
    exact stalkObjHom_comp X hX p φ ψ

/-- Objects of `stalkAlgebraFunctor` are the residue arrows `stalkAlgebraResidueHom`. -/
theorem stalkAlgebraFunctor_obj (ξ : deformationCategory Λ k X hX) :
    (stalkAlgebraFunctor Λ k X hX p).obj ξ = Over.mk (stalkAlgebraResidueHom X hX p ξ) :=
  rfl

/-- `stalkAlgebraFunctor` lies strictly over `ArtinianLocalAlgCat`. -/
theorem stalkAlgebraFunctor_comp_forget :
    stalkAlgebraFunctor Λ k X hX p ⋙
        FlatAlgebraCat.deformationForget Λ k (structureStalk X hX p) =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k :=
  stalkFunctor_comp_forget X hX p

variable (Λ k) in
/-- The stalk functor as a morphism of categories over `C_Λ`, landing in
`Def_{structureStalk}`. -/
def stalkAlgebraBasedFunctor :
    BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k) ⥤ᵇ
      BasedCategory.ofFunctor
        (FlatAlgebraCat.deformationForget Λ k (structureStalk X hX p)) :=
  BasedFunctor.ofFunctor (stalkAlgebraFunctor Λ k X hX p)
    (stalkAlgebraFunctor_comp_forget X hX p)

/-- The underlying ordinary functor of `stalkAlgebraBasedFunctor` is
`stalkAlgebraFunctor`. -/
theorem stalkAlgebraBasedFunctor_toFunctor :
    (stalkAlgebraBasedFunctor Λ k X hX p).toFunctor = stalkAlgebraFunctor Λ k X hX p :=
  rfl

/-- `stalkAlgebraBasedFunctor` lies over the scheme-level slice projection. -/
theorem stalkAlgebraBasedFunctor_w :
    (stalkAlgebraBasedFunctor Λ k X hX p).toFunctor ⋙
        FlatAlgebraCat.deformationForget Λ k (structureStalk X hX p) =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k :=
  (stalkAlgebraBasedFunctor Λ k X hX p).w

/-- Taking stalks of a deformation does not change the Artinian local base. -/
theorem stalkAlgebraBasedFunctor_obj_base (ξ : deformationCategory Λ k X hX) :
    ((stalkAlgebraBasedFunctor Λ k X hX p).toFunctor.obj ξ).left.base = ξ.left.base :=
  rfl

end FlatSchemeCat

end
