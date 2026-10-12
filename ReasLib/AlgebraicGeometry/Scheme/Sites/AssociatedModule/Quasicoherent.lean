/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Standard

/-!
# Quasi-coherence of associated modules on scheme sites

This module proves that pullback sections of a quasi-coherent module form a
quasi-coherent sheaf of modules on the standard big, small Zariski, and small
étale sites of a scheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.StandardTopology.Big

/-- The associated module of a quasi-coherent module is quasi-coherent on every
standard big scheme site. -/
instance associatedModule_isQuasicoherent
    (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    (associatedModule τ S F).IsQuasicoherent := sorry

end AlgebraicGeometry.StandardTopology.Big

namespace AlgebraicGeometry.Scheme.Zariski.Small

/-- The associated module of a quasi-coherent module is quasi-coherent on the
small Zariski site. -/
instance associatedModule_isQuasicoherent
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    (associatedModule S F).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Zariski.Small

namespace AlgebraicGeometry.Scheme.Etale.Small

/-- The associated module of a quasi-coherent module is quasi-coherent on the
small étale site. -/
instance associatedModule_isQuasicoherent
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    (associatedModule S F).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Etale.Small

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The associated module of a quasi-coherent module is quasi-coherent on both
the small Zariski and small étale sites. -/
theorem small_isQuasicoherent
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    (Zariski.Small.associatedModule S F).IsQuasicoherent ∧
      (Etale.Small.associatedModule S F).IsQuasicoherent :=
  ⟨Zariski.Small.associatedModule_isQuasicoherent S F,
    Etale.Small.associatedModule_isQuasicoherent S F⟩

/-- The uniform associated module is quasi-coherent on every standard big scheme site. -/
theorem instIsQuasicoherentBig
    (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    (big τ S F).IsQuasicoherent := by
  change (StandardTopology.Big.associatedModule τ S F).IsQuasicoherent
  infer_instance

/-- The uniform associated module is quasi-coherent on either canonical small
scheme site. -/
instance instIsQuasicoherentSmall
    (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    (small σ S F).IsQuasicoherent := by
  cases σ
  · change (Zariski.Small.associatedModule S F).IsQuasicoherent
    infer_instance
  · change (Etale.Small.associatedModule S F).IsQuasicoherent
    infer_instance

end AlgebraicGeometry.Scheme.AssociatedModule
