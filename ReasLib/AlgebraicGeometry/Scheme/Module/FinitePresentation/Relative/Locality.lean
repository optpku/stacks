module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative

/-!
# Locality of relative finite presentation for scheme modules

Relative finite presentation of a quasicoherent scheme module can be tested on compatible
affine opens and is preserved by restriction to compatible opens.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a locally finite type morphism and a quasicoherent module, relative finite presentation
is equivalent to relative finite presentation of sections on every compatible affine-open pair. -/
theorem isFinitePresentationOver_iff_affineOpenSections
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] :
    F.IsFinitePresentationOver f ↔
      ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
        ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
          @Module.FinitePresentationRelativeTo
            Γ(S, V) Γ(X, U) Γ(F, U) _ _ (Scheme.Hom.sectionsAlgebra f V U e) _ _ := sorry

namespace IsFinitePresentationOver

/-- Relative finite presentation of a quasicoherent module is preserved after restriction to
compatible source and target opens. -/
theorem restrict
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] (hF : F.IsFinitePresentationOver f)
    {U : X.Opens} {V : S.Opens} (e : U ≤ f ⁻¹ᵁ V) :
    (F.restrict U.ι).IsFinitePresentationOver (f.resLE V U e) := sorry

end IsFinitePresentationOver
end AlgebraicGeometry.Scheme.Modules
