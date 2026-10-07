module

import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.TwistedGlobalSections.QuasiCompact
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 28.28.5 (1): if `Proj 𝒜` is quasi-compact and `F` is quasi-coherent, the
canonical counit from the sheaf associated to
`⨁ n : ℤ, Γ(F ⊗ Proj.AssociatedModule.twistingSheaf 𝒜 n, ⊤)` to `F` is an isomorphism. -/
@[stacks 0AG5] #check
  (AlgebraicGeometry.ProjTwistedGlobalSections.counit_isIso :
    ∀ {A : Type u} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      (F : (AlgebraicGeometry.Proj 𝒜).Modules) [CompactSpace (AlgebraicGeometry.Proj 𝒜)]
      [F.IsQuasicoherent] (C : AlgebraicGeometry.ProjTwistedGlobalSections 𝒜 F),
      IsIso C.counit)

/- Lemma 28.28.5 (2): if the degree-one projective standard opens cover `Proj 𝒜`, the
map induced by the canonical counit on every degree-`n` twisted-global-sections component is
the identity. -/
@[stacks 0AG5] #check
  (AlgebraicGeometry.ProjTwistedGlobalSections.degreeMap_eq_id_of_degreeOpen_one_eq_top :
    ∀ {A : Type u} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      (F : (AlgebraicGeometry.Proj 𝒜).Modules) [CompactSpace (AlgebraicGeometry.Proj 𝒜)]
      [F.IsQuasicoherent] (C : AlgebraicGeometry.ProjTwistedGlobalSections 𝒜 F),
      AlgebraicGeometry.Proj.degreeOpen 𝒜 1 = ⊤ → ∀ n : ℤ,
        C.degreeMap n = AddMonoidHom.id
          (AlgebraicGeometry.ProjTwistedGlobalSections.degree 𝒜 F n))
