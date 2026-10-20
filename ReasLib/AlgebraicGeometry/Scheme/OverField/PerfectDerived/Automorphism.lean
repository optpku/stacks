module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.PullbackTensor
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.Sibling

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- An exact linear endofunctor of perfect complexes on a proper regular scheme over a
field that fixes every coherent module with zero-dimensional support is sibling to derived
pullback by a topologically trivial automorphism over the field followed by tensoring with an
invertible module. -/
theorem exists_idOnSpace_automorphism_invertible_areSiblings
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [Scheme.Regular X.left]
    (F : PerfectDerived X ⥤ PerfectDerived X) [F.Linear k] [F.CommShift ℤ]
    (h_exact : F.HasTriangulatedStructure)
    (hF : ∀ (ℱ : X.left.Modules) [SheafOfModules.IsCoherent ℱ],
      topologicalKrullDim (moduleSupport ℱ) = 0 →
        Nonempty (ofCoherentModule X ℱ ≅ F.obj (ofCoherentModule X ℱ))) :
    ∃ (φ : X ⟶ X) (_ : IsIso φ),
      φ.left.base = 𝟙 X.left.toTopCat ∧
        ∃ (L : X.left.Modules) (_ : Scheme.Modules.Invertible L),
          areSiblings F (pullbackTensorInvertible φ L) h_exact
            (pullbackTensorInvertible_hasTriangulatedStructure φ L) := sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
