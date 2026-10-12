/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure

/-!
# Coherence of subquotients

Coherent modules on a locally Noetherian scheme are closed under quasi-coherent
subobjects and quotients.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A quasi-coherent subobject of a coherent module on a locally Noetherian scheme is
coherent. -/
theorem isCoherent_subobject_of_isQuasicoherent
    (ℱ : X.Modules) [ℱ.IsCoherent] (𝒢 : Subobject ℱ)
    [((𝒢 : X.Modules)).IsQuasicoherent] :
    ((𝒢 : X.Modules)).IsCoherent := sorry

/-- A quasi-coherent quotient of a coherent module on a locally Noetherian scheme is
coherent. -/
theorem isCoherent_of_epi_from_coherent
    {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsQuasicoherent]
    (π : ℱ ⟶ 𝒢) [Epi π] :
    𝒢.IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
