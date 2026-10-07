module

public import stacks_project.Chap66.Lemma_66_26_1_Pullback
import StacksCheckRecall

/-!
# Lemma 66.26.1

For an étale morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, one has
`f_small⁻¹ 𝒪_Y = 𝒪_X` and `f^* 𝒢 = f_small⁻¹ 𝒢` for sheaves of `𝒪_Y`-modules, and in
particular `f^* : Mod(𝒪_Y) ⥤ Mod(𝒪_X)` is exact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Sheaf.InternalModule

universe u

/- Lemma 66.26.1 (1): `f_small⁻¹ 𝒪_Y = 𝒪_X` as an isomorphism of the inverse-image structure
map of `ringedToposHom f`. -/
@[stacks 03LV] #check
  (ringedToposHom_structureMap_isIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      IsIso (ringedToposHom f).structureMap)

/- Lemma 66.26.1 (2): `f^* 𝒢 = f_small⁻¹ 𝒢` on underlying sheaves, for any sheaf of
`𝒪_Y`-modules `𝒢`. -/
@[stacks 03LV] #check
  (Modules.pullbackIsoInverseImage :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      Modules.pullback f ⋙ ToInternal.underlying (structureSheaf X) ≅
        ToInternal.underlying (structureSheaf Y) ⋙ etaleRestrictionSheaf f (Type u))

/- Lemma 66.26.1 (3): in particular, `f^* : Mod(𝒪_Y) ⥤ Mod(𝒪_X)` is exact. -/
@[stacks 03LV] #check
  (Modules.pullback_exact :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      exactFunctor Y.Modules X.Modules (Modules.pullback f))
