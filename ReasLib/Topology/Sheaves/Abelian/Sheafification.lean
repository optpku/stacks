/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sheaves.Abelian
public import ReasLib.CategoryTheory.Sites.TypeSheafification

/-!
# Sheafification of abelian-group-valued presheaves on topological spaces

The opens site of a topological space admits the canonical sheafification of
`AddCommGrpCat`-valued presheaves.  Registering this globally avoids rebuilding the same local
instance at every use of abelian sheaves on a space.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Limits

universe w u

namespace TopCat

/-- Abelian-group-valued presheaves on the opens site of a topological space admit
sheafification. -/
noncomputable instance addCommGrpHasSheafify (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u w} := by
  -- Local instance justification (proof-local temporary data): The plus-plus adjunction requires the forgetful functor to preserve the cover-indexed colimit for every open U.
  letI : ∀ (U : Opens X), PreservesColimitsOfShape
      ((Opens.grothendieckTopology X).Cover U)ᵒᵖ
      (forget AddCommGrpCat.{max u w}) := fun U => by
    -- Local instance justification (proof-local temporary data): Essential smallness of the opposite cover category supplies the coefficient-universe FinallySmall witness needed for filtered-colimit preservation.
    letI : FinallySmall.{max u w}
        ((Opens.grothendieckTopology X).Cover U)ᵒᵖ :=
      finallySmall_of_essentiallySmall _
    exact FinallySmall.preservesColimitsOfShape_of_isFiltered
      (((Opens.grothendieckTopology X).Cover U)ᵒᵖ)
      (forget AddCommGrpCat.{max u w})
  exact HasSheafify.mk' (J := Opens.grothendieckTopology X)
    (A := AddCommGrpCat.{max u w})
    (plusPlusAdjunction (Opens.grothendieckTopology X) (AddCommGrpCat.{max u w}))

/-- On an opens site, the weak equivalences inverted by abelian sheafification are exactly the
locally bijective morphisms. -/
@[stacks 03DF "local bijectivity for abelian sheaves on opens"]
noncomputable instance addCommGrpWEqualsLocallyBijective (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u w} := by
  -- Local instance justification (proof-local temporary data): The weak-equivalence characterization consumes local injectivity of every abelian sheafification unit, transported here from its underlying type-valued unit.
  letI : ∀ P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u w},
      Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
        (toSheafify (Opens.grothendieckTopology X) P) := by
    intro P
    rw [← Presheaf.isLocallyInjective_forget_iff]
    rw [← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    -- Local instance justification (proof-local temporary data): Local injectivity of the underlying type-valued sheafification unit feeds composition through the plus-plus and forgetful comparison isomorphisms.
    letI := GrothendieckTopology.toSheafify_isLocallyInjective_type_of_univLE
      (Opens.grothendieckTopology X) (P ⋙ forget AddCommGrpCat.{max u w})
    infer_instance
  -- Local instance justification (proof-local temporary data): The weak-equivalence characterization consumes local surjectivity of every abelian sheafification unit, established by factoring its underlying map through two plus stages and the comparison isomorphisms.
  letI : ∀ P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u w},
      Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        (toSheafify (Opens.grothendieckTopology X) P) := by
    intro P
    rw [Presheaf.isLocallySurjective_iff_whisker_forget]
    rw [← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    dsimp [GrothendieckTopology.toSheafify]
    rw [GrothendieckTopology.plusMap_toPlus]
    -- Local instance justification (proof-local temporary data): Local surjectivity of the first type-valued plus unit is the first factor in the displayed two-stage sheafification map.
    letI h₁ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        ((Opens.grothendieckTopology X).toPlus
          (P ⋙ forget AddCommGrpCat.{max u w})) :=
      GrothendieckTopology.toPlus_isLocallySurjective_type
        (Opens.grothendieckTopology X) (P ⋙ forget AddCommGrpCat.{max u w})
    -- Local instance justification (proof-local temporary data): Local surjectivity of the plus unit on the first plus object is the second factor in the displayed two-stage sheafification map.
    letI h₂ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        ((Opens.grothendieckTopology X).toPlus
          ((Opens.grothendieckTopology X).plusObj
            (P ⋙ forget AddCommGrpCat.{max u w}))) :=
      GrothendieckTopology.toPlus_isLocallySurjective_type
        (Opens.grothendieckTopology X)
          ((Opens.grothendieckTopology X).plusObj
            (P ⋙ forget AddCommGrpCat.{max u w}))
    -- Local instance justification (proof-local temporary data): The composite of the two locally surjective plus units supplies the premise for transporting surjectivity to type-valued sheafification.
    letI h₁₂ := Presheaf.isLocallySurjective_comp
      (Opens.grothendieckTopology X)
      ((Opens.grothendieckTopology X).toPlus
        (P ⋙ forget AddCommGrpCat.{max u w}))
      ((Opens.grothendieckTopology X).toPlus
        ((Opens.grothendieckTopology X).plusObj
          (P ⋙ forget AddCommGrpCat.{max u w})))
    -- Local instance justification (proof-local temporary data): The plus-plus-to-sheafification comparison isomorphism is locally surjective and is the next factor after the two plus units.
    letI h₃ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        (plusPlusIsoSheafify (Opens.grothendieckTopology X)
          (Type (max u w)) (P ⋙ forget AddCommGrpCat.{max u w})).hom :=
      Presheaf.isLocallySurjective_of_iso _ _
    -- Local instance justification (proof-local temporary data): Composing the two plus units with their sheafification comparison supplies local surjectivity of the underlying type-valued unit for the final transport.
    letI h₁₃ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        (((Opens.grothendieckTopology X).toPlus (P ⋙ forget AddCommGrpCat.{max u w}) ≫
          (Opens.grothendieckTopology X).toPlus
            ((Opens.grothendieckTopology X).plusObj
              (P ⋙ forget AddCommGrpCat.{max u w}))) ≫
          (plusPlusIsoSheafify (Opens.grothendieckTopology X)
            (Type (max u w)) (P ⋙ forget AddCommGrpCat.{max u w})).hom) :=
      Presheaf.isLocallySurjective_comp _ _ _
    -- Local instance justification (proof-local temporary data): The forgetful sheafification comparison isomorphism is locally surjective, allowing the final composite to recover the abelian sheafification unit.
    letI h₄ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        (sheafifyComposeIso (Opens.grothendieckTopology X)
          (forget AddCommGrpCat.{max u w}) P).hom :=
      Presheaf.isLocallySurjective_of_iso _ _
    exact Presheaf.isLocallySurjective_comp
      (Opens.grothendieckTopology X)
      (((Opens.grothendieckTopology X).toPlus (P ⋙ forget AddCommGrpCat.{max u w}) ≫
          (Opens.grothendieckTopology X).toPlus
            ((Opens.grothendieckTopology X).plusObj
              (P ⋙ forget AddCommGrpCat.{max u w}))) ≫
        (plusPlusIsoSheafify (Opens.grothendieckTopology X)
          (Type (max u w)) (P ⋙ forget AddCommGrpCat.{max u w})).hom)
      (sheafifyComposeIso (Opens.grothendieckTopology X)
        (forget AddCommGrpCat.{max u w}) P).hom
  exact GrothendieckTopology.WEqualsLocallyBijective.mk'
    (Opens.grothendieckTopology X) (AddCommGrpCat.{max u w})

/-- Equal-universe specialization of the canonical construction.  Its direct universe pattern
lets typeclass inference determine a space universe from the coefficient universe. -/
noncomputable instance (priority := 1100) addCommGrpHasSheafifySelf (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  addCommGrpHasSheafify.{0, u} X

/-- Equal-universe local-bijectivity law, derived from the same canonical owner. -/
noncomputable instance (priority := 1100) addCommGrpWEqualsLocallyBijectiveSelf (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  addCommGrpWEqualsLocallyBijective.{0, u} X

end TopCat
