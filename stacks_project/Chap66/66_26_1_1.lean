module

public import stacks_project.Chap66.«66_26_1_1_Restrict»
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Sheaf.InternalModule

/- 66.26.1.1 (1): `𝒢|_{X_étale}` is `Modules.restrictFunctor`. -/
@[stacks 03LW] #check
  (Modules.restrictFunctor :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      Y.Modules ⥤ X.Modules)

/- 66.26.1.1 (2): `𝒢|_{X_étale} ≅ Modules.pullback`. -/
@[stacks 03LW] #check
  (Modules.restrictFunctorIsoPullback :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      Modules.restrictFunctor f ≅ Modules.pullback f)

/- 66.26.1.1 (3): `𝒢|_{X_étale} ≅ f_small⁻¹`. -/
@[stacks 03LW] #check
  (Modules.restrictFunctorIsoInverseImage :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      Modules.restrictFunctor f ⋙ ToInternal.underlying (structureSheaf X) ≅
        ToInternal.underlying (structureSheaf Y) ⋙ etaleRestrictionSheaf f (Type u))
