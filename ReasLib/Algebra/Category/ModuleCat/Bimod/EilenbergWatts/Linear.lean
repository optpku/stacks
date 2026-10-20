module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.Algebra.Category.ModuleCat.Bimod.TensorProduct
public import ReasLib.Algebra.Category.ModuleCat.Bimod.RelativeTensor.ModuleFunctor
public import ReasLib.Algebra.Category.ModuleCat.Bimod.RelativeTensor.Functor

/-!
# Linear Eilenberg--Watts functors

This module owns the admissible-functor category and the coefficient-to-tensor-functor
construction for commuting module actions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Module.Bimodule Module.Bimodule.RelativeTensor
open scoped ModuleCat.Algebra TensorProduct

noncomputable section

universe u

namespace ModuleCat
namespace EilenbergWatts

section General

variable (R A B : Type u)
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- A functor between right-module categories is admissible when it is `R`-linear, right exact,
and preserves all coproducts indexed by a type in its universe. -/
structure Admissible
    (F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ) : Prop where
  linear : Functor.Linear R F
  rightExact : rightExactFunctor (ModuleCat Aᵐᵒᵖ) (ModuleCat Bᵐᵒᵖ) F
  preservesDirectSums : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F

/-- Construct an admissibility witness from its three defining properties. -/
def Admissible.of (F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ)
    (linear : Functor.Linear R F)
    (rightExact : rightExactFunctor (ModuleCat Aᵐᵒᵖ) (ModuleCat Bᵐᵒᵖ) F)
    (preservesDirectSums : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F) :
    Admissible R A B F :=
  { linear := linear, rightExact := rightExact, preservesDirectSums := preservesDirectSums }

/-- A module functor is admissible if and only if it is `R`-linear, right exact,
and preserves all coproducts indexed by a type in its universe. -/
theorem admissible_iff (F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ) :
    Admissible R A B F ↔
      Functor.Linear R F ∧
        rightExactFunctor (ModuleCat Aᵐᵒᵖ) (ModuleCat Bᵐᵒᵖ) F ∧
          ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F := sorry

/-- The full category of admissible `R`-linear module functors. -/
abbrev FunctorCategory :=
  ObjectProperty.FullSubcategory
    (fun F : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ ↦ Admissible R A B F)

/-- Tensoring with a fixed bimodule gives an admissible functor. -/
theorem tensorModuleFunctor_admissible (K : Type u)
    [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
    [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
    [SMulCommClass A Bᵐᵒᵖ K] :
    Admissible R A B
      (tensorModuleFunctor (R := R) (A := A) (B := B) K) := sorry

/-- Tensor a coefficient morphism in the second factor, then realize and extract the ordinary
right-module morphism. -/
noncomputable def tensorMapApp
    {K K' : ModuleCat.{u} (A ⊗[R] Bᵐᵒᵖ)} (f : K ⟶ K')
    (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (tensorModuleFunctor (R := R) (A := A) (B := B)
      (TensorProductModule (R := R) (A := A) (B := B) K)).obj M ⟶
      (tensorModuleFunctor (R := R) (A := A) (B := B)
        (TensorProductModule (R := R) (A := A) (B := B) K')).obj M :=
  (rightModuleEquivalence (R := R) (A := B)).inverse.map
    ((rightModuleFunctor (R := R) (A := B)).map
      (ModuleCat.ofHom (RelativeTensor.mapRight (R := R) (A := A) (B := B)
        (M := RightModuleFunctor.restricted (R := R) M)
        (TensorProductModule.toHom (R := R) (A := A) (B := B) f.hom))))

/-- Naturality of the tensor-map components in the module variable. -/
theorem tensorMapApp_naturality
    {K K' : ModuleCat.{u} (A ⊗[R] Bᵐᵒᵖ)} (f : K ⟶ K')
    {M M' : ModuleCat.{u} Aᵐᵒᵖ} (g : M ⟶ M') :
    (tensorModuleFunctor (R := R) (A := A) (B := B)
      (TensorProductModule (R := R) (A := A) (B := B) K)).map g ≫
        tensorMapApp (R := R) (A := A) (B := B) f M' =
      tensorMapApp (R := R) (A := A) (B := B) f M ≫
        (tensorModuleFunctor (R := R) (A := A) (B := B)
          (TensorProductModule (R := R) (A := A) (B := B) K')).map g := sorry

/-- Coefficient maps induce natural transformations between tensor functors. -/
noncomputable def tensorMap
    {K K' : ModuleCat.{u} (A ⊗[R] Bᵐᵒᵖ)} (f : K ⟶ K') :
    tensorModuleFunctor (R := R) (A := A) (B := B)
        (TensorProductModule (R := R) (A := A) (B := B) K) ⟶
      tensorModuleFunctor (R := R) (A := A) (B := B)
        (TensorProductModule (R := R) (A := A) (B := B) K') where
  app := tensorMapApp R A B f
  naturality := fun {X Y} g => tensorMapApp_naturality R A B f g

/-- Coefficient identity maps act identically on tensor functors. -/
theorem tensorMap_id {K : ModuleCat.{u} (A ⊗[R] Bᵐᵒᵖ)} :
    tensorMap (R := R) (A := A) (B := B) (𝟙 K) = 𝟙 _ := sorry

/-- Tensor maps preserve composition. -/
theorem tensorMap_comp {K K' K'' : ModuleCat.{u} (A ⊗[R] Bᵐᵒᵖ)}
    (f : K ⟶ K') (g : K' ⟶ K'') :
    tensorMap (R := R) (A := A) (B := B) (f ≫ g) =
      tensorMap (R := R) (A := A) (B := B) f ≫
        tensorMap (R := R) (A := A) (B := B) g := sorry

/-- The coefficient-to-admissible-functor assignment. -/
noncomputable def tensorFunctor :
    ModuleCat.{u} (A ⊗[R] Bᵐᵒᵖ) ⥤ FunctorCategory R A B where
  obj K :=
    { obj := tensorModuleFunctor (R := R) (A := A) (B := B)
        (TensorProductModule (R := R) (A := A) (B := B) K)
      property := tensorModuleFunctor_admissible R A B
        (TensorProductModule (R := R) (A := A) (B := B) K) }
  map f := by
    change _ ⟶ _
    exact ObjectProperty.homMk (tensorMap (R := R) (A := A) (B := B) f)
  map_id K := by
    apply ObjectProperty.hom_ext
    exact tensorMap_id (R := R) (A := A) (B := B) (K := K)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact tensorMap_comp (R := R) (A := A) (B := B) f g

/-- Tensoring identifies coefficient modules with admissible module functors. -/
noncomputable instance tensorFunctorIsEquivalence :
    (tensorFunctor R A B).IsEquivalence := sorry

end General

variable (R A B : Type u)
variable [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- The coefficient-ring equivalence from `A ⊗[R] Bᵐᵒᵖ` to `A ⊗[R] B`. -/
noncomputable def commutativeCoefficientEquiv :
    A ⊗[R] Bᵐᵒᵖ ≃+* A ⊗[R] B :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[R] A)
    (AlgEquiv.toOpposite R B).symm).toRingEquiv

/-- The tensor functor from coefficient modules over `A ⊗[R] B` to admissible
module functors for commutative algebras. -/
noncomputable def commutativeTensorFunctor :
    ModuleCat.{u} (A ⊗[R] B) ⥤ FunctorCategory R A B :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (commutativeCoefficientEquiv (R := R) (A := A) (B := B))).functor ⋙
    tensorFunctor R A B

/-- The commutative tensor functor is an equivalence of categories. -/
noncomputable instance commutativeTensorFunctorIsEquivalence :
    (commutativeTensorFunctor R A B).IsEquivalence :=
  inferInstanceAs ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (commutativeCoefficientEquiv R A B)).functor ⋙ tensorFunctor R A B).IsEquivalence

end EilenbergWatts
end ModuleCat
