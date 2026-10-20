module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Biproduct
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure

/-!
# Coherence of biproducts and kernels on schemes

Binary biproducts and kernels of morphisms between coherent module sheaves on a scheme
are coherent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The binary biproduct of coherent module sheaves on a scheme is coherent. -/
instance instIsCoherentBiprod {X : Scheme.{u}}
    (F₁ F₂ : X.Modules) [F₁.IsCoherent] [F₂.IsCoherent] :
    (F₁ ⊞ F₂).IsCoherent := sorry

/-- The kernel of a morphism between coherent module sheaves on a scheme is coherent. -/
instance instIsCoherentKernel {X : Scheme.{u}}
    {F₁ F₂ : X.Modules} [F₁.IsCoherent] [F₂.IsCoherent] (φ : F₁ ⟶ F₂) :
    (kernel φ).IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
