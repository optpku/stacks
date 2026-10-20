module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject.Derived.Functor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject.Derived.Representable
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

/-!
# Derived tensor-representable adjunction over an algebra sheaf

The sectionwise tensor-representable adjunction is compatible with quasi-isomorphisms on both
sides.  Its total left- and right-derived functors therefore form the canonical adjunction
between derived DG modules over `endDGA K` and the derived category of `O`-module sheaves.
-/

@[expose] public section

noncomputable section

universe r u v w z

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg.TensorWithObject.Derived

-- Use the existing standard localization for the actual underlying ring-sheaf carrier.
attribute [local instance] RingedSite.Hom.RingPresentation.moduleHasDerivedCategory

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, max u z}]
variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}

/-- Derived tensor followed by the enriched representable functor retains the total
left-derived universal property. -/
@[stacks 09LY "left-derived property of arbitrary-ring tensor followed by representable"]
instance tensorRepresentable_isLeftDerived
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    (tensorFunctor K ⋙ representableFunctor K).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (tensorCounit K) (representableFunctor K))
      (DifferentialGradedModule.quasiIso (endDGA K)) := sorry

/-- The enriched representable functor followed by derived tensor retains the total
right-derived universal property. -/
@[stacks 09LY "right-derived property of arbitrary-ring representable followed by tensor"]
instance representableTensor_isRightDerived
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    (representableFunctor K ⋙ tensorFunctor K).IsRightDerivedFunctor
      (Functor.whiskerRight (representableUnit K) (tensorFunctor K) ≫
        (Functor.associator _ _ _).hom)
      (representableQis (O := O)) := sorry

/-- Lemma 22.35.5 (09LY): derived tensoring with `K` is left adjoint to the total derived
enriched representable functor `RHom(K, -)` over an arbitrary coefficient ring. -/
@[stacks 09LY "arbitrary-ring derived tensor-representable adjunction"]
noncomputable def adjunction
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    tensorFunctor K ⊣ representableFunctor K :=
  @CategoryTheory.Adjunction.derived _ _ _ _ _ _ _ _
    _ _ (TensorWithObject.homotopyAdjunction K) _ _
    (DifferentialGradedModule.quasiIso (endDGA K)) (representableQis (O := O))
    _ _ _ _ (tensorCounit K) (representableUnit K)
    (tensorFunctor_isLeftDerived K) (representableFunctor_isRightDerived K)
    (tensorRepresentable_isLeftDerived K) (representableTensor_isRightDerived K)

/-- The derived tensor functor is recognized by typeclass search as a left adjoint. -/
@[stacks 09LY "left-adjoint instance for arbitrary-ring derived tensor"]
noncomputable instance tensorFunctor_isLeftAdjoint
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    (tensorFunctor K).IsLeftAdjoint :=
  (adjunction K).isLeftAdjoint

/-- The derived representable functor is recognized by typeclass search as a right adjoint. -/
@[stacks 09LY "right-adjoint instance for arbitrary-ring derived representable"]
noncomputable instance representableFunctor_isRightAdjoint
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    (representableFunctor K).IsRightAdjoint :=
  (adjunction K).isRightAdjoint

/-- The derived representable functor inherits canonical compatibility with integer shifts from
its adjunction with derived tensor. -/
@[stacks 09LY "shift compatibility of the arbitrary-ring derived representable functor"]
noncomputable instance representableFunctor_commShift
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    (representableFunctor K).CommShift ℤ :=
  (adjunction K).rightAdjointCommShift ℤ

/-- The derived representable right adjoint is triangulated. -/
@[stacks 09LY "triangulated arbitrary-ring derived representable functor"]
instance representableFunctor_isTriangulated
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    (representableFunctor K).IsTriangulated := sorry

/-- The bifunctorial Hom equivalence of the derived tensor-representable adjunction. -/
@[stacks 09LY "arbitrary-ring derived tensor-representable Hom equivalence"]
noncomputable def homEquiv
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K]
    (M : DifferentialGradedModule.Derived.Category (endDGA K))
    (L : DerivedCategory
      (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O)) :
    ((tensorFunctor K).obj M ⟶ L) ≃ (M ⟶ (representableFunctor K).obj L) :=
  (adjunction K).homEquiv M L

section Checks

variable (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K]

#synth (representableFunctor K).CommShift ℤ
#synth (representableFunctor K).IsTriangulated
#synth (representableFunctor K).Linear R

end Checks

end SheafOfModules.CommAlg.TensorWithObject.Derived
