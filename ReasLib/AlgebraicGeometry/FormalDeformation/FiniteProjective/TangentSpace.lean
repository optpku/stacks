/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.FormalDeformation.FiniteProjective.Deformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms

/-!
# Tangent space of a finite-projective deformation category

The dual-number fibre of the finite-projective deformation category has a canonical
trivial object, and every object in that fibre is isomorphic to it.
-/

@[expose] public section

open CategoryTheory
open Functor.Fiber
open scoped DualNumber

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat.FiniteProjective

/-- The residue object of `C_Λ` has the same field structure as `k`. -/
instance instField_residueCarrier : Field (ArtinianLocalAlgCat.residue Λ k).carrier :=
  inferInstanceAs (Field k)

/-- A `k`-module is a module over the residue carrier. -/
instance instModule_residueCarrier (V : Type u) [AddCommGroup V] [Module k V] :
    Module (ArtinianLocalAlgCat.residue Λ k).carrier V :=
  inferInstanceAs (Module k V)

/-- Finite-dimensionality of `V` is preserved under the residue carrier identification. -/
instance instFiniteDimensional_residueCarrier (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    FiniteDimensional (ArtinianLocalAlgCat.residue Λ k).carrier V :=
  inferInstanceAs (FiniteDimensional k V)

/-- The finite projective residue-fibre module of `x₀ = (k, V)`. -/
abbrev moduleOf (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    ModuleCat.FiniteProjective.{u, u} (ArtinianLocalAlgCat.residue Λ k).carrier :=
  (fiberToCore (ArtinianLocalAlgCat.residue Λ k) (residueObject V)).of

/-- `moduleOf` recovers the finite projective module stored in `residueObject`. -/
theorem moduleOf_eq (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    moduleOf Λ k V = (fiberToCore (ArtinianLocalAlgCat.residue Λ k) (residueObject V)).of := rfl

/-- The trivial dual-number module `k[ε] ⊗_k V`. -/
abbrev trivialModule (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    ModuleCat.FiniteProjective.{u, u} (ArtinianLocalAlgCat.dualNumber Λ k).carrier :=
  (extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k)).obj (moduleOf Λ k V)

/-- Unfolding of `trivialModule`. -/
theorem trivialModule_eq (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    trivialModule Λ k V =
      (extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k)).obj (moduleOf Λ k V) := rfl

/-- The trivial dual-number deformation of `x₀ = (k, V)`, obtained by extension of scalars. -/
def trivialDeformation (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    (groupoids Λ k).p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k) :=
  ⟨mkObj (ArtinianLocalAlgCat.dualNumber Λ k) (trivialModule Λ k V), rfl⟩

/-- The underlying object of `trivialDeformation` is the Grothendieck pair. -/
theorem trivialDeformation_obj (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    fiberInclusion.obj (trivialDeformation Λ k V) =
      mkObj (ArtinianLocalAlgCat.dualNumber Λ k) (trivialModule Λ k V) := rfl

/-- The canonical strongly cocartesian pushforward of `x₀` along `k ⟶ k[ε]`. -/
def trivialPushforward (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    fiberInclusion.obj
        (residueObject V : (groupoids Λ k).p.Fiber (ArtinianLocalAlgCat.residue Λ k)) ⟶
      fiberInclusion.obj (trivialDeformation Λ k V) :=
  mkHom (ArtinianLocalAlgCat.residueToDualNumber Λ k) (Iso.refl _)

/-- The base map of `trivialPushforward` is `residueToDualNumber`. -/
theorem trivialPushforward_base (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    (groupoids Λ k).p.map (trivialPushforward Λ k V) =
      ArtinianLocalAlgCat.residueToDualNumber Λ k := rfl

/-- The canonical pushforward is strongly cocartesian. -/
instance instIsStronglyCocartesian_trivialPushforward (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    (groupoids Λ k).p.IsStronglyCocartesian
      (ArtinianLocalAlgCat.residueToDualNumber Λ k) (trivialPushforward Λ k V) := sorry

/-- The comparison isomorphism used to retract the trivial deformation. -/
def trivialRetractIso (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    (extendScalars (ArtinianLocalAlgCat.dualNumberToResidue Λ k)).obj (trivialModule Λ k V) ≅
      moduleOf Λ k V :=
  let e :=
    ((ModuleCat.extendScalarsComp
          (ArtinianLocalAlgCat.residueToDualNumber Λ k).toRingHom
          (ArtinianLocalAlgCat.dualNumberToResidue Λ k).toRingHom).app
        (moduleOf Λ k V).obj).symm ≪≫
      eqToIso
        (congrArg (fun h ↦ (ModuleCat.extendScalars h).obj (moduleOf Λ k V).obj)
          (RingHom.ext fun _ ↦ rfl)) ≪≫
      (ModuleCat.extendScalarsId (ArtinianLocalAlgCat.residue Λ k).carrier).app
        (moduleOf Λ k V).obj
  ObjectProperty.isoMk (ModuleCat.finiteProjective (ArtinianLocalAlgCat.residue Λ k).carrier) e

/-- The underlying module map of `trivialRetractIso` is the canonical comparison composite. -/
theorem trivialRetractIso_hom (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    (trivialRetractIso Λ k V).hom.hom =
      ((ModuleCat.extendScalarsComp
            (ArtinianLocalAlgCat.residueToDualNumber Λ k).toRingHom
            (ArtinianLocalAlgCat.dualNumberToResidue Λ k).toRingHom).app
          (moduleOf Λ k V).obj).symm.hom ≫
        (eqToIso
            (congrArg (fun h ↦ (ModuleCat.extendScalars h).obj (moduleOf Λ k V).obj)
              (RingHom.ext fun _ ↦ rfl))).hom ≫
          ((ModuleCat.extendScalarsId
              (ArtinianLocalAlgCat.residue Λ k).carrier).app (moduleOf Λ k V).obj).hom := rfl

/-- The unique dual-number lift of `V` in the deformation slice. -/
def trivialLift (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    (deformation V).p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k) :=
  ⟨Over.mk (mkHom (ArtinianLocalAlgCat.dualNumberToResidue Λ k) (trivialRetractIso Λ k V)), rfl⟩

/-- `trivialLift` is the over-object associated to the canonical retraction. -/
theorem trivialLift_mk (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    fiberInclusion.obj (trivialLift Λ k V) =
      Over.mk (mkHom (ArtinianLocalAlgCat.dualNumberToResidue Λ k) (trivialRetractIso Λ k V)) :=
  rfl

/-- The zero tangent vector of `Def_V`. -/
def trivialTangent (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    CategoryTheory.Functor.tangentSpace (Λ := Λ) (k := k) (deformation V).p :=
  CategoryTheory.Functor.tangentSpace.mk (Λ := Λ) (k := k) (deformation V).p (trivialLift Λ k V)

/-- `trivialTangent` is the class of `trivialLift`. -/
theorem trivialTangent_spec (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    trivialTangent Λ k V = CategoryTheory.Functor.tangentSpace.mk (Λ := Λ) (k := k) (deformation V).p (trivialLift Λ k V) := rfl

/-- Every tangent class is the canonical trivial class. -/
theorem eq_trivialTangent (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (x : CategoryTheory.Functor.tangentSpace (Λ := Λ) (k := k) (deformation V).p) : x = trivialTangent Λ k V := sorry

end ArtinianLocalAlgCat.FiniteProjective
