/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Refinement
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleNeighborhood

/- Lemma 37.35.3 (1): two étale neighborhoods of a point admit a common
refining neighborhood with morphisms to both. -/
@[stacks 057A]
#check (AlgebraicGeometry.Scheme.EtaleNeighborhood.exists_commonRefinement :
  ∀ {S : Scheme.{u}} {s : S} (U₁ U₂ : EtaleNeighborhood S s),
    ∃ U : EtaleNeighborhood S s, Nonempty (Hom U U₁ × Hom U U₂))

/- Lemma 37.35.3 (2): parallel neighborhood morphisms inducing the same
transported residue-field map become equal after a further refinement. -/
@[stacks 057A]
#check (AlgebraicGeometry.Scheme.EtaleNeighborhood.exists_equalizingRefinement_of_residueFieldMap_eq :
  ∀ {S : Scheme.{u}} {s : S} {U U' : EtaleNeighborhood S s}
    (h₁ h₂ : Hom U U'),
    ((Scheme.residueFieldCongr h₁.map_point).inv ≫
      Scheme.Hom.residueFieldMap h₁.toEtaleHom.left U.point =
      (Scheme.residueFieldCongr h₂.map_point).inv ≫
        Scheme.Hom.residueFieldMap h₂.toEtaleHom.left U.point) →
      ∃ (U'' : EtaleNeighborhood S s) (h : Hom U'' U), h ≫ h₁ = h ≫ h₂)

end AlgebraicGeometry.Scheme.EtaleNeighborhood
