module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Subquotient
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.9.3 (1): on a locally Noetherian scheme, every quasi-coherent submodule of a
coherent module is coherent. -/
@[stacks 01Y1] #check
  (AlgebraicGeometry.Scheme.Modules.isCoherent_subobject_of_isQuasicoherent :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      (ℱ : X.Modules) [ℱ.IsCoherent] (𝒢 : Subobject ℱ)
      [((𝒢 : X.Modules)).IsQuasicoherent],
      ((𝒢 : X.Modules)).IsCoherent)

/- Lemma 30.9.3 (2): on a locally Noetherian scheme, every quasi-coherent quotient of a
coherent module is coherent. -/
@[stacks 01Y1] #check
  (AlgebraicGeometry.Scheme.Modules.isCoherent_of_epi_from_coherent :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsQuasicoherent]
      (π : ℱ ⟶ 𝒢) [Epi π],
      𝒢.IsCoherent)
