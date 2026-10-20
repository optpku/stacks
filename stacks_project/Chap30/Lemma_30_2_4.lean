module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffinePushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 30.2.4: Let `f : X ⟶ S` be an affine morphism of schemes and let `ℱ` be a
quasi-coherent `𝒪_X`-module. Then the cohomology of `ℱ` on `X` is isomorphic in every degree to
the cohomology of its pushforward on `S`. -/
@[stacks 089W] #check
  (AlgebraicGeometry.Scheme.globalCohomology_iso_pushforward_of_isAffineHom :
    ∀ {X S : Scheme.{u}}
      (f : X ⟶ S) [IsAffineHom f]
      [HasInjectiveResolutions X.Modules]
      [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u})]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (i : ℕ),
      IsIsomorphic
        (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' i (⊤ : Opens X))
        (((SheafOfModules.toSheaf S.ringCatSheaf).obj
          ((Scheme.Modules.pushforward f).obj ℱ)).H' i (⊤ : Opens S)))

end AlgebraicGeometry.Scheme
