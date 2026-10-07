module

import StacksCheckRecall
public import stacks_project.Chap66.Lemma_66_21_3
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap73.Remark_73_4_14_Ringed
public import stacks_project.Chap73.Remark_73_4_14_StructureSheaf

/-!
# Remark 73.4.14

The sites `(Spaces/X)_étale` and `X_spaces,étale` carry structure sheaves, and the
morphisms `i_f`, `π_X`, `i_X`, `f_small`, and `f_big` upgrade to morphisms of
ringed sites (respectively topoi).
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open scoped MorphismOfTopoiIn

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)

/- The small spaces-étale structure sheaf of Properties of Spaces, Section 66.21. -/
#check spacesStructureSheaf

#check spacesRingedSite

/- the structure sheaf `𝒪` on `(Spaces/X)_étale` is `U ↦ Γ(U, 𝒪_U)`. -/
@[stacks 0DF9] #check
  (Big.structureSheaf :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      Sheaf (overEtaleTopology X) RingCat.{u})

@[stacks 0DF9] #check
  (Big.structureSheaf_obj :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (U : Over X),
      (Big.structureSheaf X).obj.obj (op U) = Big.gamma U.left)

/- The comparison `𝒪_Y ⟶ i_f⁻¹ 𝒪`, objectwise `spacesStructureToGamma`. Its inverse is the
source map `i_f^♯ : i_f⁻¹ 𝒪 ⟶ 𝒪_Y`. -/
#check
  (SpacesToBig.relocalizationStructureSheafMap f :
    spacesStructureSheaf Y ⟶
      (SpacesToBig.relocalizationPushforward f).obj (Big.structureSheaf X))

/- Remark 73.4.14 (1): `i_f` is the morphism of topoi
`Sh(Y_spaces,étale) ⟶ Sh((Spaces/X)_étale)`, and `i_f^♯ : i_f⁻¹ 𝒪 ⟶ 𝒪_Y` is the inverse
of `relocalizationStructureSheafMap f`. -/
@[stacks 0DF9] #check
  (SpacesToBig.relocalizationMorphismOfTopoi f :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      (overEtaleTopology X) (spacesEtaleTopology Y))

@[stacks 0DF9] #check
  (SpacesToBig.relocalizationStructureSheafMap_isIso f :
    IsIso (SpacesToBig.relocalizationStructureSheafMap f))

/- Remark 73.4.14 (2): `i_X` is the special case of `i_f` with `f = 𝟙 X`. -/
@[stacks 0DF9] #check
  (SpacesToBig.identityRelocalization X :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      (overEtaleTopology X) (spacesEtaleTopology X))

@[stacks 0DF9] #check
  (SpacesToBig.identityRelocalization_eq X :
    SpacesToBig.identityRelocalization X =
      SpacesToBig.relocalizationMorphismOfTopoi (𝟙 X))

@[stacks 0DF9] #check
  (SpacesToBig.relocalizationStructureSheafMap_isIso (𝟙 X) :
    IsIso (SpacesToBig.relocalizationStructureSheafMap (𝟙 X)))

/- Remark 73.4.14 (3): `π_X` upgrades to a morphism of ringed sites with
`π_X^♯ : 𝒪_X ⟶ π_{X,*} 𝒪` the comparison `(π_{X,*} 𝒪)(U) = 𝒪(U) = 𝒪_X(U)`. -/
@[stacks 0DF9] #check
  (SpacesToBig.siteHom X :
    RingedSite.Hom (Big.ringedSite X) (spacesRingedSite X))

@[stacks 0DF9] #check
  (SpacesToBig.siteSharp_app X :
    ∀ U : spacesEtaleSite X,
      (SpacesToBig.siteSharp X).hom.app (op U) = Big.spacesStructureToGamma U)

/- Remark 73.4.14 (4): the extension of `f_small` to a morphism of ringed topoi is
Properties of Spaces, Lemma 66.21.3. -/
@[stacks 0DF9] #check
  (ringedToposHom :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
      (X ⟶ Y) → RingedSite.ToposHom
        (AlgebraicGeometry.AlgebraicSpace.ringedSite X)
        (AlgebraicGeometry.AlgebraicSpace.ringedSite Y))

#check
  (spacesRingedToposHom :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
      (X ⟶ Y) → RingedSite.ToposHom (spacesRingedSite X) (spacesRingedSite Y))

/- Remark 73.4.14 (5): `f_big` upgrades to a morphism of ringed topoi
`Sh((Spaces/Y)_étale) ⟶ Sh((Spaces/X)_étale)`, and
`f_big^♯ : f_big⁻¹ 𝒪_X ⟶ 𝒪_Y` is an isomorphism. -/
@[stacks 0DF9] #check
  (Big.ringedHom f : RingedSite.ToposHom (Big.ringedSite Y) (Big.ringedSite X))

@[stacks 0DF9] #check
  (Big.sharp f :
    (Big.mapPushforward f).obj (Big.structureSheaf X) ⟶ Big.structureSheaf Y)

@[stacks 0DF9] #check
  (Big.sharp_isIso f : IsIso (Big.sharp f))
