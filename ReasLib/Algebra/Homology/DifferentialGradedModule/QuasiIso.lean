/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Forget
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy

/-!
# Homology and Quasi-isomorphisms in the DG Homotopy Category

The underlying-complex functor descends from right differential graded modules to their homotopy
category.  Composing it with Mathlib's homotopy-category homology functors gives the canonical
degreewise homology API and the associated quasi-isomorphism predicate.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape DifferentialGradedCategory
open scoped DifferentialGradedCategory

universe u v

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}

namespace Homotopy

/-- Homotopic closed differential graded module maps induce the same morphism between the
underlying complexes in Mathlib's homotopy category. -/
theorem forget_map_sound {L M : DifferentialGradedModule.{u, v} A}
    {f g : CompHom L M} (h : Homotopic L M f g) :
    (HomotopyCategory.quotient (ModuleCat.{v} R) (up ℤ)).map
        (compHomToHom f).toCochainMap =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (up ℤ)).map
        (compHomToHom g).toCochainMap := sorry

/-- Forget the differential graded algebra action on the homotopy category and retain the
underlying cochain complex up to ordinary cochain homotopy. -/
def forget (A : CochainDGAlgebra R) :
    K R (DifferentialGradedModule.{u, v} A) ⥤
      HomotopyCategory (ModuleCat.{v} R) (up ℤ) where
  obj X :=
    (HomotopyCategory.quotient (ModuleCat.{v} R) (up ℤ)).obj
      X.obj.toCochainComplex
  map {X Y} f :=
    Quotient.lift
      (fun g : CompHom X.obj Y.obj ↦
        (HomotopyCategory.quotient (ModuleCat.{v} R) (up ℤ)).map
          (compHomToHom g).toCochainMap)
      (fun _ _ h ↦ forget_map_sound h) f
  map_id := sorry
  map_comp := sorry

/-- The underlying-homotopy functor sends an object to its underlying cochain complex. -/
@[simp]
theorem forget_obj (A : CochainDGAlgebra R)
    (X : K R (DifferentialGradedModule.{u, v} A)) :
    (forget A).obj X =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (up ℤ)).obj
        X.obj.toCochainComplex := sorry

/-- The underlying-homotopy functor maps a represented class by forgetting the action. -/
@[simp]
theorem forget_map_rep (A : CochainDGAlgebra R)
    {L M : DifferentialGradedModule.{u, v} A} (f : CompHom L M) :
    (forget A).map f.toHomotopyClass =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (up ℤ)).map
        (compHomToHom f).toCochainMap := sorry

/-- Forgetting to the ordinary homotopy category is additive. -/
instance forget_additive (A : CochainDGAlgebra R) :
    (forget.{u, v} A).Additive := sorry

/-- The degree-`n` homology functor on the differential graded homotopy category. -/
noncomputable def homologyFunctor (A : CochainDGAlgebra R) (n : ℤ) :
    K R (DifferentialGradedModule.{u, v} A) ⥤ ModuleCat.{v} R :=
  forget A ⋙ HomotopyCategory.homologyFunctor (ModuleCat.{v} R) (up ℤ) n

/-- Degreewise homology on the differential graded homotopy category is additive. -/
@[stacks 09KX "additivity of homology on the DG homotopy category"]
noncomputable instance homologyFunctorAdditive (A : CochainDGAlgebra R) (n : ℤ) :
    (homologyFunctor.{u, v} A n).Additive := sorry

/-- Degreewise homology on the differential graded homotopy category is `R`-linear. -/
@[stacks 09KX "linearity of homology on the DG homotopy category"]
noncomputable instance homologyFunctorLinear (A : CochainDGAlgebra R) (n : ℤ) :
    Functor.Linear R (homologyFunctor.{u, v} A n) := sorry

/-- Homology on the differential graded homotopy category, evaluated on a strict module,
agrees with the homology of its underlying cochain complex. -/
@[stacks 09KX "homotopy-category homology of a strict DG module"]
noncomputable def homologyIso (A : CochainDGAlgebra R)
    (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (homologyFunctor A n).obj ((DifferentialGradedModule.toK A).obj M) ≅
      M.homology n :=
  (HomotopyCategory.homologyFunctorFactors
    (ModuleCat.{v} R) (up ℤ) n).app M.toCochainComplex

/-- The forward strict-model comparison is the hom component of Mathlib's homology
factorization through the ordinary homotopy category. -/
@[simp]
theorem homologyIso_hom (A : CochainDGAlgebra R)
    (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (homologyIso A M n).hom =
      (HomotopyCategory.homologyFunctorFactors
        (ModuleCat.{v} R) (up ℤ) n).hom.app M.toCochainComplex := sorry

/-- The inverse strict-model comparison is the inverse component of Mathlib's homology
factorization through the ordinary homotopy category. -/
@[simp]
theorem homologyIso_inv (A : CochainDGAlgebra R)
    (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (homologyIso A M n).inv =
      (HomotopyCategory.homologyFunctorFactors
        (ModuleCat.{v} R) (up ℤ) n).inv.app M.toCochainComplex := sorry

/-- The strict-model homology comparison is natural in strict differential graded module
morphisms. -/
@[stacks 09KX "naturality of strict DG-module homology comparison"]
theorem homologyIso_hom_naturality (A : CochainDGAlgebra R)
    {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) (n : ℤ) :
    (homologyFunctor A n).map ((DifferentialGradedModule.toK A).map f) ≫
        (homologyIso A N n).hom =
      (homologyIso A M n).hom ≫
        (DifferentialGradedModule.homologyFunctor A n).map f := sorry

/-- The inverse strict-model homology comparison is natural in strict differential graded
module morphisms. -/
@[stacks 09KX "inverse naturality of strict DG-module homology comparison"]
theorem homologyIso_inv_naturality (A : CochainDGAlgebra R)
    {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) (n : ℤ) :
    (homologyIso A M n).inv ≫
        (homologyFunctor A n).map ((DifferentialGradedModule.toK A).map f) =
      (DifferentialGradedModule.homologyFunctor A n).map f ≫
        (homologyIso A N n).inv := sorry

/-- The degree-`n` homology map induced by a morphism in the differential graded homotopy
category. -/
noncomputable abbrev homologyMap {X Y : K R (DifferentialGradedModule.{u, v} A)}
    (f : X ⟶ Y) (n : ℤ) :
    (homologyFunctor A n).obj X ⟶ (homologyFunctor A n).obj Y :=
  (homologyFunctor A n).map f

/-- The homology map of an identity morphism is the identity. -/
@[simp]
theorem homologyMap_id (X : K R (DifferentialGradedModule.{u, v} A)) (n : ℤ) :
    homologyMap (A := A) (𝟙 X) n = 𝟙 _ := sorry

/-- Homology maps respect composition. -/
@[simp]
theorem homologyMap_comp {X Y Z : K R (DifferentialGradedModule.{u, v} A)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ) :
    homologyMap (A := A) (f ≫ g) n =
      homologyMap (A := A) f n ≫ homologyMap (A := A) g n := sorry

#synth (homologyFunctor.{u, v} A 0).Additive
#synth Functor.Linear R (homologyFunctor.{u, v} A 0)

end Homotopy

/-- A morphism in the differential graded homotopy category is a quasi-isomorphism when every
degreewise homology map is an isomorphism. -/
def quasiIso (A : CochainDGAlgebra R) :
    MorphismProperty (K R (DifferentialGradedModule.{u, v} A)) :=
  fun _ _ f ↦ ∀ n : ℤ, IsIso (Homotopy.homologyMap f n)

namespace QuasiIso

/-- Membership in `quasiIso A` is exactly invertibility on homology in every degree. -/
theorem iff {X Y : K R (DifferentialGradedModule.{u, v} A)} (f : X ⟶ Y) :
    quasiIso A f ↔ ∀ n : ℤ, IsIso (Homotopy.homologyMap f n) := sorry

/-- Every degreewise homology functor inverts quasi-isomorphisms. -/
theorem isInvertedBy_homologyFunctor (A : CochainDGAlgebra R) (n : ℤ) :
    (quasiIso A).IsInvertedBy (Homotopy.homologyFunctor.{u, v} A n) := sorry

/-- Quasi-isomorphisms contain all identity morphisms. -/
instance containsIdentities (A : CochainDGAlgebra R) :
    (quasiIso.{u, v} A).ContainsIdentities := sorry

/-- Quasi-isomorphisms are closed under composition. -/
instance isMultiplicative (A : CochainDGAlgebra R) :
    (quasiIso.{u, v} A).IsMultiplicative := sorry

/-- Quasi-isomorphisms satisfy the two-out-of-three property. -/
instance hasTwoOutOfThree (A : CochainDGAlgebra R) :
    (quasiIso.{u, v} A).HasTwoOutOfThreeProperty := sorry

/-- Quasi-isomorphisms are stable under retracts. -/
instance isStableUnderRetracts (A : CochainDGAlgebra R) :
    (quasiIso.{u, v} A).IsStableUnderRetracts := sorry

end QuasiIso

/-- Compatibility alias for the degreewise characterization of a quasi-isomorphism. -/
theorem quasiIso_iff {X Y : K R (DifferentialGradedModule.{u, v} A)} (f : X ⟶ Y) :
    quasiIso A f ↔ ∀ n : ℤ, IsIso (Homotopy.homologyMap f n) := sorry

end DifferentialGradedModule
