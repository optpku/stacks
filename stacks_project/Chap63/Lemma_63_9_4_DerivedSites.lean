module

public import stacks_project.Chap63.Lemma_63_9_4_Transport

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.Scheme.Compactification

noncomputable section
universe u v

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  (C : CompDiagram X g) (Λ : Type u) [CommRing Λ]

/-- The alternate fixed-interior spelling uses the original interior sheafification. -/
instance instHasSheafify_ofInteriorHom
    [HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)] :
    HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
  inferInstanceAs (HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))

/-- Slice sheafification uses the same underlying site, without choosing a second instance. -/
instance instHasWeakSheafify_ofInteriorHom_over
    [∀ U : (CompDiagram.interior X g C).Etale,
      HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    (U : (ofInteriorHom X g C).obj.right.left.Etale) :
    HasWeakSheafify ((ofInteriorHom X g C).obj.right.left.smallEtaleTopology.over U)
      (ModuleCat.{u} Λ) :=
  inferInstanceAs (HasWeakSheafify
    ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ))

/-- The two spellings of the same interior use the same localization data and universe. -/
instance instHasDerivedCategory_ofInteriorHom
    [HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ U : (CompDiagram.interior X g C).Etale,
      HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory.{v} (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))] :
    HasDerivedCategory.{v}
      (Sheaf (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  inferInstanceAs (HasDerivedCategory.{v}
    (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)))

variable {X' Y' Z' : Scheme.{u}} (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
  (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X.left)
  (h_upper : IsPullback c f' X.hom b) (h_lower : IsPullback b g' g a)
  [IsSeparated f'] [Scheme.Hom.FiniteType f']
  [IsSeparated g'] [Scheme.Hom.FiniteType g']
  [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace Y'] [QuasiSeparatedSpace Y']
  [CompactSpace Z'] [QuasiSeparatedSpace Z']

/-- The base compactification in the pulled-back diagram has the already chosen ambient. -/
theorem stacked_P_g_ambient_eq :
    (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left =
      ambient g a g' b h_lower C.P_g := by
  rw [stackedCompPullback_def]
  rfl

/-- Reuse the lower ambient sheafification on the pulled-back base compactification. -/
instance instHasSheafify_stacked_P_g
    [HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)] :
    HasSheafify
      (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ) := by
  rw [stacked_P_g_ambient_eq]
  infer_instance

/-- Reuse the lower ambient's slice sheafification on the same scheme. -/
instance instHasWeakSheafify_stacked_P_g_over
    [∀ U : (ambient g a g' b h_lower C.P_g).Etale,
      HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    (U : (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale) :
    HasWeakSheafify
      ((stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U)
      (ModuleCat.{u} Λ) := by
  revert U
  rw [stackedCompPullback_def]
  intro U
  exact inferInstanceAs (HasWeakSheafify
    ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ))

/-- The pulled-back base compactification reuses the lower ambient's localization data. -/
instance instHasDerivedCategory_stacked_P_g
    [HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ U : (ambient g a g' b h_lower C.P_g).Etale,
      HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory.{v}
      (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))] :
    HasDerivedCategory.{v}
      (Sheaf (stackedCompPullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
        (ModuleCat.{u} Λ)) := by
  rw [stacked_P_g_ambient_eq]
  infer_instance

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek
end
