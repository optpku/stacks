/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

/-!
# Derived base change on modules and triangulated lifts
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right

namespace CategoryTheory.ModuleCat.DerivedBaseChange

/-- The object of `D(R')` obtained by viewing an `A`-module `M` in `D(A)`, restricting
along `R → A`, and then applying derived extension of scalars `- ⊗[R]^L R'`. -/
noncomputable abbrev obj (R R' A : Type u) [CommRing R] [CommRing R'] [CommRing A]
    [Algebra R R'] [Algebra R A] (M : ModuleCat.{u, u} A) :
    DerivedCategory (ModuleCat.{u, u} R') :=
  (derivedExtensionOfScalars (algebraMap R R')).obj
    ((derivedRestrictionOfScalars (algebraMap R A)).obj (single0 M))

/-- `obj R R' A M` is the image of the degree-zero embedding of `M` under derived
restriction along `R → A` followed by derived extension along `R → R'`. -/
theorem obj_eq (R R' A : Type u) [CommRing R] [CommRing R'] [CommRing A]
    [Algebra R R'] [Algebra R A] (M : ModuleCat.{u, u} A) :
    obj R R' A M =
      (derivedExtensionOfScalars (algebraMap R R')).obj
        ((derivedRestrictionOfScalars (algebraMap R A)).obj (single0 M)) := sorry

/-- A functor `T : D(A) ⥤ D(A ⊗[R] R')` lifts derived base change on modules if it is
triangulated and, for every `A`-module `M`, the image of `T(single0 M)` under
`D(A ⊗[R] R') ⥤ D(R')` is isomorphic to `obj R R' A M`. -/
structure LiftsOnModules {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    [Algebra R R'] [Algebra R A]
    (T : DerivedCategory (ModuleCat.{u, u} A) ⥤
      DerivedCategory (ModuleCat.{u, u} (A ⊗[R] R'))) : Prop where
  /-- `T` admits some shift comparison making it a triangulated functor. -/
  hasTriangulatedStructure : T.HasTriangulatedStructure
  /-- After derived restriction `D(A ⊗[R] R') ⥤ D(R')`, `T` sends `single0 M`
  to `obj R R' A M`. -/
  mapsModule (M : ModuleCat.{u, u} A) :
    Nonempty
      ((derivedRestrictionOfScalars (algebraMap R' (A ⊗[R] R'))).obj
          (T.obj (single0 M)) ≅
        obj R R' A M)

/-- A triangulated-structure witness and objectwise restriction isomorphisms define
a lift of derived base change on modules. -/
def LiftsOnModules.of {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    [Algebra R R'] [Algebra R A]
    {T : DerivedCategory (ModuleCat.{u, u} A) ⥤
      DerivedCategory (ModuleCat.{u, u} (A ⊗[R] R'))}
    (hasTriangulatedStructure : T.HasTriangulatedStructure)
    (mapsModule : ∀ M : ModuleCat.{u, u} A,
      Nonempty
        ((derivedRestrictionOfScalars (algebraMap R' (A ⊗[R] R'))).obj
            (T.obj (single0 M)) ≅
          obj R R' A M)) :
    LiftsOnModules T where
  hasTriangulatedStructure := hasTriangulatedStructure
  mapsModule := mapsModule

/-- Lifting on modules is equivalent to triangulated structure together with an
objectwise isomorphism after derived restriction to `D(R')`. -/
theorem liftsOnModules_iff {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    [Algebra R R'] [Algebra R A]
    (T : DerivedCategory (ModuleCat.{u, u} A) ⥤
      DerivedCategory (ModuleCat.{u, u} (A ⊗[R] R'))) :
    LiftsOnModules T ↔
      T.HasTriangulatedStructure ∧
        ∀ M : ModuleCat.{u, u} A,
          Nonempty
            ((derivedRestrictionOfScalars (algebraMap R' (A ⊗[R] R'))).obj
                (T.obj (single0 M)) ≅
              obj R R' A M) := sorry

/-- There exist commutative rings with maps `R → R'` and `R → A` for which no
triangulated functor `D(A) ⥤ D(A ⊗[R] R')` realizes derived base change on every
`A`-module after restriction to `D(R')`. -/
theorem exists_not_exists_functor :
    ∃ (R R' A : Type u) (_ : CommRing R) (_ : CommRing R') (_ : CommRing A)
      (_ : Algebra R R') (_ : Algebra R A),
      ¬ ∃ (T : DerivedCategory (ModuleCat.{u, u} A) ⥤
            DerivedCategory (ModuleCat.{u, u} (A ⊗[R] R'))),
          LiftsOnModules T := sorry

/-- Not every pair of commutative-ring maps `R → R'` and `R → A` admits a
triangulated functor `D(A) ⥤ D(A ⊗[R] R')` realizing derived base change on modules
after restriction to `D(R')`. -/
theorem not_forall_exists_functor :
    ¬ ∀ (R R' A : Type u) [CommRing R] [CommRing R'] [CommRing A]
        [Algebra R R'] [Algebra R A],
      ∃ (T : DerivedCategory (ModuleCat.{u, u} A) ⥤
          DerivedCategory (ModuleCat.{u, u} (A ⊗[R] R'))),
        LiftsOnModules T := sorry

end CategoryTheory.ModuleCat.DerivedBaseChange
