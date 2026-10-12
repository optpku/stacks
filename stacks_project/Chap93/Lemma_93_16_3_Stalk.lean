/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReasLib.RingTheory.Henselian.Pair.Completion
public import stacks_project.Chap93.Lemma_93_9_8_Stalk

/-!
# Structure-sheaf stalks as `k`-algebras, with henselization and completion

The type synonym `structureStalk` carries the `hX`-dependent `k`-algebra
structure on `O_{X, p}`. Henselization and adic completion of that local ring
are the residue rings of the second and third arrows in Lemma 93.16.3.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing RingPairCat
open scoped BasedFunctor

universe u

noncomputable section

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The slice projection `Def_P ⥤ C_Λ` of Example 93.8.1, over the residue
object of Definition 90.16.8. -/
abbrev deformationForget (P : Type u) [CommRing P] [Algebra k P] :
    deformationCategory Λ k P ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget

/-- `deformationForget` sends a deformation `(A, Q)` to the Artinian local algebra `A`. -/
theorem deformationForget_obj (P : Type u) [CommRing P] [Algebra k P]
    (ξ : deformationCategory Λ k P) :
    (deformationForget Λ k P).obj ξ = ξ.left.base :=
  sorry

end FlatAlgebraCat

namespace FlatSchemeCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : Scheme.{u})
  (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
variable (p : X)

/-- The structure-sheaf stalk `O_{X, p}` as a type synonym, so that the
`k`-algebra structure coming from `hX` can be registered as an instance. -/
def structureStalk : Type u :=
  (fun _ ↦ (X.presheaf.stalk p : Type u)) hX

/-- `structureStalk` is the structure-sheaf stalk at `p`. -/
theorem structureStalk_eq : structureStalk X hX p = X.presheaf.stalk p :=
  sorry

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
  sorry

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
  sorry

/-- Scalar multiplication of `k` on `O_{X, p}^∧` factors through `O_{X, p}`. -/
theorem algebraMap_completeStalk (x : k) :
    algebraMap k (completeStalk X hX p) x =
      algebraMap (structureStalk X hX p) (completeStalk X hX p)
        (algebraMap k (structureStalk X hX p) x) :=
  sorry

section Henselization

variable [henselianPairInclusion.IsRightAdjoint]

/-- The henselization `O_{X, p}^h` of the local ring at `p`. -/
abbrev henselStalk : Type u :=
  henselizationRing (pairOfIdeal (maximalIdeal (structureStalk X hX p)))

/-- `henselStalk` is the pair henselization of `(O_{X, p}, m_p)`. -/
theorem henselStalk_eq :
    henselStalk X hX p =
      henselizationRing (pairOfIdeal (maximalIdeal (structureStalk X hX p))) :=
  sorry

/-- The `k`-algebra structure on `O_{X, p}^h` via `k → O_{X, p} → O_{X, p}^h`. -/
instance instAlgebra_k_henselStalk : Algebra k (henselStalk X hX p) :=
  (RingHom.comp (toHenselization (pairOfIdeal (maximalIdeal (structureStalk X hX p))))
    (algebraMap k (structureStalk X hX p))).toAlgebra

/-- Scalar multiplication of `k` on `O_{X, p}^h` factors through `O_{X, p}`. -/
theorem algebraMap_henselStalk (x : k) :
    algebraMap k (henselStalk X hX p) x =
      algebraMap (structureStalk X hX p) (henselStalk X hX p)
        (algebraMap k (structureStalk X hX p) x) :=
  sorry

/-- Pair henselization of a Noetherian local stalk remains Noetherian. -/
instance instIsNoetherianRing_henselStalk [IsNoetherianRing (structureStalk X hX p)] :
    IsNoetherianRing (henselStalk X hX p) :=
  henselizationRing_isNoetherian (pairOfIdeal (maximalIdeal (structureStalk X hX p)))

end Henselization

variable [AlgebraicGeometry.Flat hX]

/-- The pair `(A, O_{Y, schemeHom p})` attached to a deformation `(A, Y)` of `X`,
as a flat algebra over `A` with residue ring `structureStalk`. -/
def stalkAlgebraObj (ξ : deformationCategory Λ k X hX) : FlatAlgebraCat Λ k where
  base := ξ.left.base
  algebra := (ξ.left.scheme.presheaf.stalk (ξ.hom.schemeHom p) : Type u)
  isAlgebra := instAlgebra_structureStalk ξ.left (ξ.hom.schemeHom p)
  isFlat := sorry

/-- `stalkAlgebraObj` keeps the Artinian local base of the original deformation. -/
theorem stalkAlgebraObj_base (ξ : deformationCategory Λ k X hX) :
    (stalkAlgebraObj X hX p ξ).base = ξ.left.base :=
  sorry

/-- The residue arrow `(A, O_{Y, schemeHom p}) ⟶ (k, O_{X, p})` induced by
`schemeHom.stalkMap` at `p`, targeting `ofResidue` of `structureStalk`. -/
def stalkAlgebraResidueHom (ξ : deformationCategory Λ k X hX) :
    stalkAlgebraObj X hX p ξ ⟶ FlatAlgebraCat.ofResidue Λ k (structureStalk X hX p) where
  baseHom := ξ.hom.baseHom
  toRingHom := (ξ.hom.schemeHom.stalkMap p).hom
  commutes := sorry
  isIso_tensor := sorry

/-- `stalkAlgebraResidueHom` keeps the underlying morphism of Artinian local
algebras. -/
theorem stalkAlgebraResidueHom_baseHom (ξ : deformationCategory Λ k X hX) :
    (stalkAlgebraResidueHom X hX p ξ).baseHom = ξ.hom.baseHom :=
  sorry

/-- A morphism of deformations of `X` induces the corresponding stalk map of
structure sheaves at the preimage of `p`. -/
def stalkAlgebraObjHom {ξ η : deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    stalkAlgebraObj X hX p ξ ⟶ stalkAlgebraObj X hX p η where
  baseHom := φ.left.baseHom
  toRingHom :=
    (eqToHom
          (congrArg (fun x ↦ ξ.left.scheme.presheaf.stalk x)
            (congrArg (fun h ↦ h.schemeHom p) (Over.w φ)).symm) ≫
        φ.left.schemeHom.stalkMap (η.hom.schemeHom p)).hom
  commutes := sorry
  isIso_tensor := sorry

/-- `stalkAlgebraObjHom` keeps the underlying morphism of Artinian local algebras. -/
theorem stalkAlgebraObjHom_baseHom {ξ η : deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    (stalkAlgebraObjHom X hX p φ).baseHom = φ.left.baseHom :=
  sorry

variable (Λ k) in
/-- The functor `Def_X ⥤ Def_{O_{X, p}}` sending a deformation `(A, Y)` of `X`
to the stalk pair `(A, O_{Y, schemeHom p})` over `structureStalk`. -/
def stalkAlgebraFunctor :
    deformationCategory Λ k X hX ⥤
      FlatAlgebraCat.deformationCategory Λ k (structureStalk X hX p) where
  obj ξ := Over.mk (stalkAlgebraResidueHom X hX p ξ)
  map φ := Over.homMk (stalkAlgebraObjHom X hX p φ) sorry
  map_id := sorry
  map_comp := sorry

/-- Objects of `stalkAlgebraFunctor` are the residue arrows `stalkAlgebraResidueHom`. -/
theorem stalkAlgebraFunctor_obj (ξ : deformationCategory Λ k X hX) :
    (stalkAlgebraFunctor Λ k X hX p).obj ξ = Over.mk (stalkAlgebraResidueHom X hX p ξ) :=
  sorry

/-- `stalkAlgebraFunctor` lies strictly over `ArtinianLocalAlgCat`. -/
theorem stalkAlgebraFunctor_comp_forget :
    stalkAlgebraFunctor Λ k X hX p ⋙
        FlatAlgebraCat.deformationForget Λ k (structureStalk X hX p) =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k :=
  sorry

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
  sorry

/-- `stalkAlgebraBasedFunctor` lies over the scheme-level slice projection. -/
theorem stalkAlgebraBasedFunctor_w :
    (stalkAlgebraBasedFunctor Λ k X hX p).toFunctor ⋙
        FlatAlgebraCat.deformationForget Λ k (structureStalk X hX p) =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k :=
  sorry

/-- Taking stalks of a deformation does not change the Artinian local base. -/
theorem stalkAlgebraBasedFunctor_obj_base (ξ : deformationCategory Λ k X hX) :
    ((stalkAlgebraBasedFunctor Λ k X hX p).toFunctor.obj ξ).left.base = ξ.left.base :=
  sorry

end FlatSchemeCat

end
