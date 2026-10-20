module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.FinitePresentation

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

namespace QuotPoint

/-- Forget proper support, sending a Quot-point to its underlying finitely
presented quotient point. -/
def toFpPoint {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) : FpPoint f F σ where
  point := Q.point
  isFinitePresentation := Q.isFinitePresentation

/-- Forgetting proper support preserves the underlying quotient point. -/
theorem toFpPoint_spec {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) :
    Q.toFpPoint.point = Q.point := sorry

end QuotPoint

/-- Forgetting proper support preserves kernel identification of Quot-points. -/
theorem toFpPoint_rel (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    (σ : SchemeOver B) :
    ∀ (Q₁ Q₂ : QuotPoint f F σ),
      (quotSetoid f F σ).r Q₁ Q₂ →
        (fpSetoid f F σ).r Q₁.toFpPoint Q₂.toFpPoint := sorry

/-- The natural transformation from the Quot functor to the finitely presented
quotient functor that forgets proper support. -/
def quotFpι (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] : quot f F ⟶ fpFunctor f F where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.toFpPoint)
        (toFpPoint_rel f F σ.unop))
  naturality := sorry

/-- The inclusion of Quot-classes into finitely presented quotient classes is
the setoid map induced by forgetting proper support. -/
theorem quotFpι_app (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] (σ : (SchemeOver B)ᵒᵖ) :
    (quotFpι f F).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.toFpPoint)
          (toFpPoint_rel f F σ.unop)) := sorry

/-- The inclusion of Quot-classes into quotient classes factors through the
finitely presented quotient classes. -/
theorem quotι_eq_quotFpι_comp_fpι (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] :
    quotι f F = quotFpι f F ≫ fpι f F := sorry

/-- Each component of the inclusion of Quot-classes into finitely presented
quotient classes is injective. -/
theorem quotFpι_app_injective (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] (σ : (SchemeOver B)ᵒᵖ) :
    Function.Injective ((quotFpι f F).app σ) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
