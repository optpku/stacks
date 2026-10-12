/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject.Triangulated
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.FromModules
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.KProjective
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Enriched
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated

/-!
# Derived tensoring with a complex over an algebra sheaf

For a complex `K` of modules over a sheaf of commutative `R`-algebras, this file derives the
explicit DG functor `- ⊗_(endDGA K) K`.  The target is the canonical derived category of module
sheaves and the scalar ring remains the arbitrary coefficient ring `R`.
-/

@[expose] public section

noncomputable section

universe r u v w z

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg.TensorWithObject.Derived

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, max u z}]
variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}

/-- Tensoring on enriched homotopy categories, followed by the canonical derived localization. -/
@[stacks 09LX "homotopy-level derived tensor over a coefficient ring"]
abbrev tensorSourceFunctor (K : Complex.{r, u, v, w, max u z} O) :=
  (TensorWithObject.tensorFunctor K).mapK ⋙
    SheafOfModules.CommAlg.Derived.Q O

/-- The homotopy-level derived tensor source is linear over the coefficient ring. -/
@[stacks 09LX "linearity of the derived tensor source"]
noncomputable instance tensorSourceFunctor_linear
    (K : Complex.{r, u, v, w, max u z} O) : (tensorSourceFunctor K).Linear R := sorry

/-- The existence condition for the total left-derived tensor functor. -/
@[stacks 09LX "existence of derived tensor over a coefficient ring"]
abbrev HasTensorFunctor (K : Complex.{r, u, v, w, max u z} O) : Prop :=
  Functor.LeftDerived.EverywhereDefined (tensorSourceFunctor K)
    (DifferentialGradedModule.quasiIso (endDGA K))

/-- Property-(P) resolutions make tensoring with `K` left derivable at every object. -/
@[stacks 09LX "property-P existence of derived tensor"]
instance hasTensorFunctor (K : Complex.{r, u, v, w, max u z} O) :
    HasTensorFunctor K := sorry

/-- The canonical source-definedness instance used by all total derived tensor constructions.

Naming this endpoint keeps typeclass search fast and pins the same derived-functor witness in
`tensorFunctor`, `tensorCounit`, and their shift compatibility. -/
@[stacks 09LX "left-derived existence for the tensor source"]
instance tensorSourceFunctor_hasLeftDerivedFunctor
    (K : Complex.{r, u, v, w, max u z} O) :
    (tensorSourceFunctor K).HasLeftDerivedFunctor
      (DifferentialGradedModule.quasiIso (endDGA K)) := sorry

/-- Lemma 22.35.3 (09LX): the total left-derived functor `- ⊗^L_(endDGA K) K`. -/
@[stacks 09LX "derived tensor with an algebra-sheaf complex"]
noncomputable def tensorFunctor (K : Complex.{r, u, v, w, max u z} O) :
    DifferentialGradedModule.Derived.Category (endDGA K) ⥤
      DerivedCategory
        (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O) :=
  (tensorSourceFunctor K).totalLeftDerived
    (DifferentialGradedModule.Derived.Q (endDGA K))
    (DifferentialGradedModule.quasiIso (endDGA K))

/-- The total derived tensor functor is linear over the coefficient ring. -/
@[stacks 09LX "linearity of derived tensor over the coefficient ring"]
noncomputable instance tensorFunctor_linear
    (K : Complex.{r, u, v, w, max u z} O) : (tensorFunctor K).Linear R := sorry

/-- The canonical comparison from derived tensoring to homotopy-level tensoring. -/
@[stacks 09LX "derived tensor comparison transformation over a coefficient ring"]
noncomputable def tensorCounit (K : Complex.{r, u, v, w, max u z} O) :
    DifferentialGradedModule.Derived.Q (endDGA K) ⋙ tensorFunctor K ⟶
      tensorSourceFunctor K :=
  (tensorSourceFunctor K).totalLeftDerivedCounit
    (DifferentialGradedModule.Derived.Q (endDGA K))
    (DifferentialGradedModule.quasiIso (endDGA K))

/-- A property-(P) module computes derived tensor without replacing the source module. -/
@[stacks 09LX "property-P objects compute derived tensor"]
theorem tensorComputesAt (K : Complex.{r, u, v, w, max u z} O)
    (M : TensorWithObject.Modules K)
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    Functor.LeftDerived.ComputesAt (tensorSourceFunctor K)
      (DifferentialGradedModule.quasiIso (endDGA K))
      ((DifferentialGradedModule.toK (endDGA K)).obj M) := sorry

/-- The derived-to-strict tensor comparison is invertible on a property-(P) module. -/
@[stacks 09LX "property-P derived tensor comparison is invertible"]
theorem tensorCounitApp_isIso (K : Complex.{r, u, v, w, max u z} O)
    (M : TensorWithObject.Modules K)
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    IsIso ((tensorCounit K).app
      ((DifferentialGradedModule.toK (endDGA K)).obj M)) := sorry

/-- The canonical derived-to-strict tensor comparison on a property-(P) module. -/
@[stacks 09LX "property-P derived tensor comparison isomorphism"]
noncomputable def tensorCounitAppIso (K : Complex.{r, u, v, w, max u z} O)
    (M : TensorWithObject.Modules K)
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    (tensorFunctor K).obj
        ((DifferentialGradedModule.Derived.fromModules (endDGA K)).obj M) ≅
      (tensorSourceFunctor K).obj
        ((DifferentialGradedModule.toK (endDGA K)).obj M) :=
  @asIso _ _ _ _
    ((tensorCounit K).app ((DifferentialGradedModule.toK (endDGA K)).obj M))
    (tensorCounitApp_isIso K M hM)

/-- The forward map of `tensorCounitAppIso` is the derived tensor counit component. -/
@[reassoc (attr := simp), stacks 09LX "forward property-P derived tensor comparison"]
theorem tensorCounitAppIso_hom (K : Complex.{r, u, v, w, max u z} O)
    (M : TensorWithObject.Modules K)
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    (tensorCounitAppIso K M hM).hom =
      (tensorCounit K).app
        ((DifferentialGradedModule.toK (endDGA K)).obj M) := sorry

/-- The inverse map of `tensorCounitAppIso` is the inverse of the derived tensor counit component. -/
@[reassoc (attr := simp), stacks 09LX "inverse property-P derived tensor comparison"]
theorem tensorCounitAppIso_inv (K : Complex.{r, u, v, w, max u z} O)
    (M : TensorWithObject.Modules K)
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    (tensorCounitAppIso K M hM).inv =
      (@asIso _ _ _ _
        ((tensorCounit K).app ((DifferentialGradedModule.toK (endDGA K)).obj M))
        (tensorCounitApp_isIso K M hM)).inv := sorry

/-- On a property-(P) module, derived tensor is represented by the strict tensor complex. -/
@[stacks 09LX "property-P strict model of derived tensor"]
noncomputable def tensorModelIso (K : Complex.{r, u, v, w, max u z} O)
    (M : TensorWithObject.Modules K)
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    (tensorFunctor K).obj
        ((DifferentialGradedModule.Derived.fromModules (endDGA K)).obj M) ≅
      DerivedCategory.Q.obj ((TensorWithObject.tensorFunctor K).obj M) :=
  tensorCounitAppIso K M hM ≪≫
    SheafOfModules.CommAlg.Derived.objIso O
      ((TensorWithObject.tensorFunctor K).obj M)

/-- The forward map of `tensorModelIso` is the counit comparison followed by the derived image map. -/
@[reassoc (attr := simp), stacks 09LX "forward property-P derived tensor model comparison"]
theorem tensorModelIso_hom (K : Complex.{r, u, v, w, max u z} O)
    (M : TensorWithObject.Modules K)
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    (tensorModelIso K M hM).hom =
      (tensorCounitAppIso K M hM).hom ≫
        (SheafOfModules.CommAlg.Derived.objIso O
          ((TensorWithObject.tensorFunctor K).obj M)).hom := sorry

/-- The inverse map of `tensorModelIso` reverses the derived image and counit comparisons. -/
@[reassoc (attr := simp), stacks 09LX "inverse property-P derived tensor model comparison"]
theorem tensorModelIso_inv (K : Complex.{r, u, v, w, max u z} O)
    (M : TensorWithObject.Modules K)
    (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    (tensorModelIso K M hM).inv =
      (SheafOfModules.CommAlg.Derived.objIso O
          ((TensorWithObject.tensorFunctor K).obj M)).inv ≫
        (tensorCounitAppIso K M hM).inv := sorry

/-- The concrete functor and its counit form a total left-derived functor model. -/
@[stacks 09LX "derived tensor universal property over a coefficient ring"]
instance tensorFunctor_isLeftDerived (K : Complex.{r, u, v, w, max u z} O) :
    (tensorFunctor K).IsLeftDerivedFunctor (tensorCounit K)
      (DifferentialGradedModule.quasiIso (endDGA K)) := sorry

/-- The standard homotopy presentation of the derived tensor source. -/
@[stacks 09LX "homotopy presentation of the derived tensor source"]
noncomputable abbrev tensorHomotopySource (K : Complex.{r, u, v, w, max u z} O) :
    DifferentialGradedCategory.K R (TensorWithObject.Modules K) ⥤
      DerivedCategory
        (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O) :=
  TensorWithObject.homotopyFunctor K ⋙
    (DerivedCategory.Qh :
      TensorWithObject.TargetHomotopy.{r, u, v, w, z} (R := R) (J := J) (O := O) ⥤
        DerivedCategory
          (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O))

/-- The homotopy and enriched presentations of the derived tensor source are canonically
identified by associativity of composition. -/
@[stacks 09LX "derived tensor source presentation isomorphism"]
noncomputable def tensorSourceIso (K : Complex.{r, u, v, w, max u z} O) :
    tensorHomotopySource K ≅ tensorSourceFunctor K :=
  Functor.associator _ _ _

/-- The derived tensor source commutes with integer shifts. -/
@[stacks 09LX "derived tensor source commutes with shifts"]
noncomputable instance tensorSourceFunctor_commShift
    (K : Complex.{r, u, v, w, max u z} O) : (tensorSourceFunctor K).CommShift ℤ :=
  Functor.CommShift.ofIso (tensorSourceIso K) ℤ

/-- The total derived tensor functor commutes with integer shifts. -/
@[stacks 09LX "derived tensor commutes with shifts"]
noncomputable instance tensorFunctor_commShift
    (K : Complex.{r, u, v, w, max u z} O) : (tensorFunctor K).CommShift ℤ :=
  Functor.totalLeftDerived_commShift (tensorSourceFunctor K)
    (DifferentialGradedModule.quasiIso (endDGA K))
    (DifferentialGradedModule.Derived.Q (endDGA K))

/-- The total derived tensor functor is triangulated. -/
@[stacks 09LX "derived tensor is triangulated"]
instance tensorFunctor_isTriangulated
    (K : Complex.{r, u, v, w, max u z} O) : (tensorFunctor K).IsTriangulated := sorry

section Checks

variable (K : Complex.{r, u, v, w, max u z} O)

#synth (TensorWithObject.homotopyFunctor K).Linear R
#synth (tensorSourceFunctor K).Linear R
#synth (tensorSourceFunctor K).HasLeftDerivedFunctor
  (DifferentialGradedModule.quasiIso (endDGA K))
#synth (tensorFunctor K).Linear R

end Checks

end SheafOfModules.CommAlg.TensorWithObject.Derived
