module

import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Module.Pushforward
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

universe u

/- Lemma 29.11.7 (1): for an affine morphism `f : X ⟶ S`, direct image is an
equivalence from quasi-coherent `𝒪_X`-modules to quasi-coherent modules over
`f_* 𝒪_X`. -/
@[stacks 01SB] #check
  (AlgebraicGeometry.Scheme.QCoh.pushforwardAsModule.isEquivalence :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f],
      Functor.IsEquivalence
        (AlgebraicGeometry.Scheme.QCoh.pushforwardAsModule f))

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]

/- Lemma 29.11.7 (2): a module over `f_* 𝒪_X` is quasi-coherent as an
`𝒪_S`-module if and only if it is quasi-coherent as an `f_* 𝒪_X`-module. -/
@[stacks 01SB]
#check
  (AlgebraicGeometry.Scheme.QcAlgebraUnder.isQuasicoherent_iff
      (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra f) :
    ∀ ℱ : ringedSiteModuleCategory (Opens.grothendieckTopology S)
        ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf),
      ((restrictionAlong
        (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)).obj
          ℱ).IsQuasicoherent ↔
        ℱ.IsQuasicoherent)
