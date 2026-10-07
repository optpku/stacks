module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Module
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

universe u

/- Lemma 29.11.6: let `S` be a scheme and let `A` be a quasi-coherent
`𝒪_S`-algebra. Then an `A`-module is quasi-coherent as an `𝒪_S`-module if and only if it is
quasi-coherent as an `A`-module. -/
@[stacks 0H88] #check
  (AlgebraicGeometry.Scheme.QcAlgebraUnder.isQuasicoherent_iff :
    ∀ {S : Scheme.{u}} (A : S.QcAlgebraUnder)
      (ℱ : ringedSiteModuleCategory (Opens.grothendieckTopology S) A.obj.right),
      ((restrictionAlong A.obj.hom).obj ℱ).IsQuasicoherent ↔ ℱ.IsQuasicoherent)

#check
  (AlgebraicGeometry.Scheme.restrictionAlong_isQuasicoherent_iff :
    ∀ {S : Scheme.{u}} {𝒜 : Sheaf (Opens.grothendieckTopology S) CommRingCat.{u}}
      (α : S.sheaf ⟶ 𝒜)
      (h𝒜 : ((restrictionAlong α).obj
        (unitModule (Opens.grothendieckTopology S) 𝒜)).IsQuasicoherent)
      (ℱ : ringedSiteModuleCategory (Opens.grothendieckTopology S) 𝒜),
      ((restrictionAlong α).obj ℱ).IsQuasicoherent ↔ ℱ.IsQuasicoherent)
