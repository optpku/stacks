/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.TraceSection
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.Discriminant

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory SheafOfModules
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace RelativeDualizingSheaf

/-- For a finite flat morphism with invertible relative dualizing sheaf, the norm of a local generator of the different generates the discriminant ideal. -/
theorem normDifferent_eq_discriminant
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsNoetherian X] [IsNoetherian Y]
    [IsFinite f] [Flat f] [Scheme.Hom.QuasiFinite f]
    (W : f.RelativeDualizingSheaf) (τ : sections W.module.obj)
    (hτ : AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.IsTraceSection W τ)
    [Scheme.Modules.Invertible W.module.obj]
    (N : Scheme.FiniteMorphismNorm f) (hN : N.IsDeterminant) :
    ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ n : ℕ, ∃ e : Module.Basis (Fin n) Γ(X, U) Γ(Y, f ⁻¹ᵁ U),
        ∃ b : Γ(Y, f ⁻¹ᵁ U),
          (W.different τ).ideal ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ = Ideal.span {b} ∧
            Ideal.span {N.app U b} = Ideal.span {Algebra.discr Γ(X, U) e} := sorry

end RelativeDualizingSheaf
end Hom
end Scheme
end AlgebraicGeometry
