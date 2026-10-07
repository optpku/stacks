module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (ℱ : X.Modules)

/- Lemma 30.9.1: On a locally Noetherian scheme, coherence of a module is
equivalent to quasi-coherence together with finite type, finite presentation,
and the corresponding finite-module criteria on affine opens and an affine
open cover. The structure module, invertible modules, and finite locally free
modules are coherent. -/
@[stacks 01XZ] #check
  (AlgebraicGeometry.Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType ℱ :
    ℱ.IsCoherent ↔ ℱ.IsQuasicoherent ∧ ℱ.IsFiniteType)

#check
  (AlgebraicGeometry.Scheme.Modules.isCoherent_iff_isFinitePresentation ℱ :
    ℱ.IsCoherent ↔ ℱ.IsFinitePresentation)

#check
  (AlgebraicGeometry.Scheme.Modules.isCoherent_iff_isQuasicoherent_and_forall_affineOpen_finite_sections
      ℱ :
    ℱ.IsCoherent ↔
      ℱ.IsQuasicoherent ∧
        ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(ℱ, U))

#check
  (AlgebraicGeometry.Scheme.Modules.IsCoherent.iff_exists_affineOpenCover ℱ :
    ℱ.IsCoherent ↔
      ℱ.IsQuasicoherent ∧
        ∃ 𝒰 : X.AffineOpenCover,
          ∀ i : 𝒰.I₀,
            Module.Finite
              Γ(X, 𝒰.openCover.f i |>.opensRange)
              Γ(ℱ, 𝒰.openCover.f i |>.opensRange))

#check
  (AlgebraicGeometry.Scheme.Modules.structureSheaf_isCoherent X :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent)

variable (ℒ : X.Modules) [Invertible ℒ]

#check
  (AlgebraicGeometry.Scheme.Modules.isCoherent_of_isInvertible ℒ :
    ℒ.IsCoherent)

#check
  (AlgebraicGeometry.Scheme.Modules.instIsCoherentOfIsInvertible ℒ :
    ℒ.IsCoherent)

variable [SheafOfModules.IsFiniteLocallyFree ℱ]

#check
  (AlgebraicGeometry.Scheme.Modules.isCoherent_of_isFiniteLocallyFree ℱ :
    ℱ.IsCoherent)

#check
  (AlgebraicGeometry.Scheme.Modules.instIsCoherentOfIsFiniteLocallyFree ℱ :
    ℱ.IsCoherent)

variable (r : ℕ) (𝒢 : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank r 𝒢]

#check
  (AlgebraicGeometry.Scheme.Modules.isCoherent_of_isFiniteLocallyFreeOfRank r 𝒢 :
    𝒢.IsCoherent)

end AlgebraicGeometry.Scheme.Modules
