module

public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap73.Lemma_73_4_7_Relocalization
public import stacks_project.Chap73.Lemma_73_4_8_Identity
public import stacks_project.Chap73.Lemma_73_4_10_Big

/-!
# Spaces-étale and big étale comparison for a morphism of algebraic spaces

This leaf owns the cross-layer equalities relating `i_f`, `π_X`, `f_big`, and
the spaces-étale morphism of topoi induced by base change along `f : Y ⟶ X`.
-/

@[expose] public section

open CategoryTheory
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Spaces-étale relocalization factors through the big étale morphism and the
identity-base relocalization. -/
theorem morphism_eq_comp_big (f : Y ⟶ X) :
    morphismOfTopoi.{u, u + 1} f =
      MorphismOfTopoiIn.comp (Big.morphismOfTopoi f)
        (morphismOfTopoi.{u, u + 1} (𝟙 Y)) := sorry

/-- Direct image along the spaces-étale morphism of topoi evaluates a sheaf on
the base-changed spaces-étale object. -/
theorem spacesEtaleMorphismOfTopoi_pushforward_obj_obj (f : Y ⟶ X)
    (F : Sheaf (spacesEtaleTopology Y) (Type (u + 1))) (U : spacesEtaleSite X) :
    ((spacesEtaleMorphismOfTopoi f).pushforward.obj F).1.obj (op U) =
      F.1.obj (op ((spacesEtalePullback f).obj U)) := sorry

/-- The square comparing the spaces-étale and big étale morphisms of topoi
commutes. -/
theorem spacesEtaleMorphismOfTopoi_comp_site (f : Y ⟶ X) :
    MorphismOfTopoiIn.comp (spacesEtaleMorphismOfTopoi f)
        (siteMorphismOfTopoi.{u, u + 1} Y) =
      MorphismOfTopoiIn.comp (siteMorphismOfTopoi.{u, u + 1} X)
        (Big.morphismOfTopoi f) := sorry

/-- The spaces-étale morphism factors as the composite of `π_X`, the big étale
morphism, and identity-base relocalization. -/
theorem spacesEtaleMorphismOfTopoi_eq_comp_big (f : Y ⟶ X) :
    spacesEtaleMorphismOfTopoi f =
      MorphismOfTopoiIn.comp
        (MorphismOfTopoiIn.comp (siteMorphismOfTopoi.{u, u + 1} X)
          (Big.morphismOfTopoi f))
        (morphismOfTopoi.{u, u + 1} (𝟙 Y)) := sorry

/-- The spaces-étale morphism is the composite of `π_X` with spaces-étale
relocalization. -/
theorem spacesEtaleMorphismOfTopoi_eq_comp (f : Y ⟶ X) :
    spacesEtaleMorphismOfTopoi f =
      MorphismOfTopoiIn.comp (siteMorphismOfTopoi.{u, u + 1} X)
        (morphismOfTopoi.{u, u + 1} f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig
