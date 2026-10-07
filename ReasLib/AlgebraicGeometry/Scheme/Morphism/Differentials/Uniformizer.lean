module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Closure
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace.Hom
open TopCat.Sheaf.RelativeDifferentials.Stalk
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- At a closed point where a scheme over a field is smooth of relative dimension one and has
separable residue field, the differential of every uniformizer freely generates the stalk of
relative differentials. -/
theorem uniformizerDifferential_freelyGenerates
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X)
    (h_closed : x ∈ closedPoints X) (h_smooth : f.SmoothAt x)
    (h_dim : f.fiberDimensionAt x = (1 : WithBot ℕ∞))
    [h_separable : ResidueField.IsSeparableOverSpec f x]
    (s : X.presheaf.stalk x)
    (h_uniformizer : IsLocalRing.maximalIdeal
      (X.presheaf.stalk x) = Ideal.span {s}) :
    let d : X.presheaf.stalk x →
        RingedSpace.stalkModuleCat (Ω[f.toShHom]) x :=
      (derivation (inverseImageStructureSheafHomComm f.toShHom) x).d
    LinearIndependent (X.presheaf.stalk x) (fun _ : Fin 1 ↦ d s) ∧
      Submodule.span (X.presheaf.stalk x) {d s} = ⊤ := sorry

end AlgebraicGeometry.Scheme.Hom
