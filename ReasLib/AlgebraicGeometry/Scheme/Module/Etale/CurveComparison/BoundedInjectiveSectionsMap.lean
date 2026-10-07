module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.DerivedResolutionComparison

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe w

namespace BoundedInjectiveSectionsMap
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
variable [EnoughInjectives C] (F : C ⥤ D) [F.Additive]
variable (K : CochainComplex.Plus C)

/-- The actual bounded-derived unit on the displayed cochain complex. -/
def unit : DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K) ⟶
    (Functor.RightDerived.Bounded.functor F).obj (DerivedCategory.Plus.Q.obj K) :=
  Functor.RightDerived.Bounded.fromCochainMap F (K := K) (𝟙 _)

/-- Bounded-below complexes of actual injective objects compute RF. -/
theorem unit_isIso [∀ i : ℤ, Injective (K.obj.X i)] : IsIso (unit F K) := by sorry

variable (M : C) (f : ActualResolutionComparison.singleModel M ⟶ DerivedCategory.Plus.Q.obj K)
variable [∀ i : ℤ, Injective (K.obj.X i)]

/-- Apply RGamma (or another specified additive derived functor) to a GIVEN
bounded-derived sheaf arrow, using source resolution and target injective units. -/
def plusMap :
    DerivedCategory.Plus.Q.obj ((CochainComplex.Plus.extendNat D).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution M).cocomplex)) ⟶
    DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K) :=
  ActualResolutionComparison.resolutionToDerived F (injectiveResolution M) ≫
    (Functor.RightDerived.Bounded.functor F).map f ≫
      (@asIso _ _ _ _ (unit F K) (unit_isIso F K)).inv

/-- The same explicit map between the actual full derived cochain objects. -/
def map :
    DerivedCategory.Q.obj
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution M).cocomplex).extend
        ComplexShape.embeddingUpNat) ⟶
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj) :=
  ((DerivedCategory.Plus.Qh.compInclusionIso D).app ((CochainComplex.Plus.extendNat D).obj
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution M).cocomplex))).inv ≫
  (DerivedCategory.Plus.ι : DerivedCategory.Plus D ⥤ DerivedCategory D).map (plusMap F K M f) ≫
  ((DerivedCategory.Plus.Qh.compInclusionIso D).app (F.mapCochainComplexPlus.obj K)).hom

end BoundedInjectiveSectionsMap
