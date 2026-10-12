/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Basic

/-!
# Modules over quasi-coherent algebra sheaves

This file relates quasi-coherence of a module over an algebra sheaf on a scheme to
quasi-coherence after restricting scalars to the structure sheaf.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

namespace QcAlgebraUnder

/-- The category of module sheaves over the coefficient algebra of a quasi-coherent
algebra sheaf. -/
abbrev Modules (A : S.QcAlgebraUnder) :=
  ringedSiteModuleCategory (Opens.grothendieckTopology S) A.obj.right

/-- The object property selecting quasi-coherent modules over a quasi-coherent
algebra sheaf. -/
abbrev quasiCoherentModuleProperty (A : S.QcAlgebraUnder) :
    ObjectProperty A.Modules :=
  fun ℱ ↦ ℱ.IsQuasicoherent

/-- The category of quasi-coherent modules over a quasi-coherent algebra sheaf. -/
abbrev QCoh (A : S.QcAlgebraUnder) :=
  A.quasiCoherentModuleProperty.FullSubcategory

namespace QCoh

/-- The inclusion of quasi-coherent modules over an algebra sheaf into all modules
over that algebra sheaf. -/
abbrev inclusion (A : S.QcAlgebraUnder) : A.QCoh ⥤ A.Modules :=
  A.quasiCoherentModuleProperty.ι

end QCoh

/-- A module over a quasi-coherent algebra sheaf on a scheme is quasi-coherent if and only if
its restriction of scalars to the structure sheaf is quasi-coherent. -/
theorem isQuasicoherent_iff
    (A : S.QcAlgebraUnder)
    (ℱ : ringedSiteModuleCategory (Opens.grothendieckTopology S) A.obj.right) :
    ((restrictionAlong A.obj.hom).obj ℱ).IsQuasicoherent ↔ ℱ.IsQuasicoherent := sorry

end QcAlgebraUnder

section RestrictionAlong

variable {𝒜 : Sheaf (Opens.grothendieckTopology S) CommRingCat.{u}}
variable (α : S.sheaf ⟶ 𝒜)
variable (h𝒜 : ((restrictionAlong α).obj
  (unitModule (Opens.grothendieckTopology S) 𝒜)).IsQuasicoherent)

include h𝒜

/-- For a morphism from a scheme's structure sheaf to a commutative ring sheaf whose
underlying unit module is quasi-coherent, quasi-coherence of a module is equivalent to
quasi-coherence after restriction of scalars. -/
theorem restrictionAlong_isQuasicoherent_iff
    (ℱ : ringedSiteModuleCategory (Opens.grothendieckTopology S) 𝒜) :
    ((restrictionAlong α).obj ℱ).IsQuasicoherent ↔ ℱ.IsQuasicoherent := by
  let A : S.QcAlgebraUnder := ⟨Under.mk α, h𝒜⟩
  exact A.isQuasicoherent_iff ℱ

end RestrictionAlong

end AlgebraicGeometry.Scheme
