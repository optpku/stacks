module

public import Mathlib.CategoryTheory.Category.ULift
public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion.RestrictionInclusion
public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal
public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion
public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion.Restriction
public import ReasLib.CategoryTheory.Cofibered.Pushforward

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory ArtinianLocalAlgCat CompleteLocalAlgCat Functor IsLocalRing
open scoped BasedFunctor

noncomputable section

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FormalObject

/-- The maximal-adic quotient map is local and respects the residue-field identification. -/
theorem truncationToInclusion_laws (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    IsLocalHom (Ideal.Quotient.mkₐ Λ (maximalIdeal R.carrier ^ (n + 1))) ∧
    (∀ h, CompleteLocalAlgCat.residueCompat (A := R) (B := inclusion.obj (R.truncation n))
      (Ideal.Quotient.mkₐ Λ (maximalIdeal R.carrier ^ (n + 1))) h =
        CompleteLocalAlgCat.residueIsoHom R) := sorry

/-- The canonical projection from a complete local algebra to the included `n`th
maximal-adic truncation. -/
def truncationToInclusion (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    R ⟶ inclusion.obj (R.truncation n) :=
  CompleteLocalAlgCat.Hom.of (Ideal.Quotient.mkₐ Λ (maximalIdeal R.carrier ^ (n + 1)))
    (truncationToInclusion_laws R n).1
    ((truncationToInclusion_laws R n).2 (truncationToInclusion_laws R n).1)

/-- The underlying algebra map of `truncationToInclusion` is the quotient map. -/
theorem truncationToInclusion_hom (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (truncationToInclusion R n).hom =
      Ideal.Quotient.mkₐ Λ (maximalIdeal R.carrier ^ (n + 1)) := rfl

end FormalObject

namespace CategoryTheory.BasedCategory.RestrictInclusion

variable
  {X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)}

/-- Hom-universe lift of `RestrictInclusion X`, matching the object/hom constraint of
`FormalObject`. -/
abbrev total (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) :
    Type (max (u + 1) v) :=
  ULiftHom.{max (u + 1) v} (RestrictInclusion X)

/-- `total X` is the Hom-universe lift of `RestrictInclusion X`. -/
theorem total_eq :
    total X = ULiftHom.{max (u + 1) v} (RestrictInclusion X) := rfl

/-- Projection of the Hom-universe lift to `C_Λ`. -/
def projectionTotal (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) :
    total X ⥤ ArtinianLocalAlgCat Λ k :=
  (ULiftHom.down : total X ⥤ RestrictInclusion X) ⋙ projection X

/-- The lifted projection is the ordinary projection after forgetting the Hom lift. -/
theorem projectionTotal_eq :
    projectionTotal X =
      (ULiftHom.down : total X ⥤ RestrictInclusion X) ⋙ projection X := rfl

/-- The lifted restricted projection is cofibered in groupoids. -/
instance projectionTotal_op_isFiberedInGroupoids
    (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k))
    [IsFibered.InGroupoids X.p.op] :
    IsFibered.InGroupoids (projectionTotal X).op := sorry

variable {S : Type v} [Category.{v} S]
variable {proj : S ⥤ ArtinianLocalAlgCat Λ k} [IsFibered.InGroupoids proj.op]

/-- Convert a restriction of the completion to a `FormalObject.Restrict`. -/
def toFormalRestrict
    (ξ : RestrictInclusion (BasedCategory.ofFunctor (completion proj))) :
    FormalObject.Restrict proj where
  formal := ξ.obj
  base := ξ.base
  over := ξ.over

/-- Convert a `FormalObject.Restrict` to a restriction of the completion. -/
def ofFormalRestrict (ξ : FormalObject.Restrict proj) :
    RestrictInclusion (BasedCategory.ofFunctor (completion proj)) :=
  RestrictInclusion.of ξ.formal ξ.base ξ.over

/-- `toFormalRestrict` preserves the stored formal object. -/
theorem toFormalRestrict_formal
    (ξ : RestrictInclusion (BasedCategory.ofFunctor (completion proj))) :
    (toFormalRestrict ξ).formal = ξ.obj := rfl

/-- `ofFormalRestrict` preserves the stored formal object. -/
theorem ofFormalRestrict_obj (ξ : FormalObject.Restrict proj) :
    (ofFormalRestrict ξ).obj = ξ.formal := rfl

private def toFormalRestrictMap
    {ξ η : RestrictInclusion (BasedCategory.ofFunctor (completion proj))} (a : ξ ⟶ η) :
    toFormalRestrict ξ ⟶ toFormalRestrict η :=
  FormalObject.Restrict.Hom.of a.obj a.base a.over
/-- The comparison with the formal restriction preserves identities and composition. -/
theorem toFormalRestrictFunctor_laws :
    (∀ ξ : RestrictInclusion (BasedCategory.ofFunctor (completion proj)),
      toFormalRestrictMap (𝟙 ξ) = 𝟙 (toFormalRestrict ξ)) ∧
    (∀ (ξ η ζ : RestrictInclusion (BasedCategory.ofFunctor (completion proj)))
      (a : ξ ⟶ η) (b : η ⟶ ζ),
      toFormalRestrictMap (a ≫ b) = toFormalRestrictMap a ≫ toFormalRestrictMap b) := sorry
/-- The comparison functor to the evaluation carrier. -/
def toFormalRestrictFunctor :
    RestrictInclusion (BasedCategory.ofFunctor (completion proj)) ⥤ FormalObject.Restrict proj where
  obj := toFormalRestrict
  map := toFormalRestrictMap
  map_id := toFormalRestrictFunctor_laws.1
  map_comp := toFormalRestrictFunctor_laws.2 _ _ _
private def ofFormalRestrictMap {ξ η : FormalObject.Restrict proj} (a : ξ ⟶ η) :
    ofFormalRestrict ξ ⟶ ofFormalRestrict η := Hom.of a.formal a.base a.over
/-- The reverse comparison with the formal restriction preserves identities and composition. -/
theorem ofFormalRestrictFunctor_laws :
    (∀ ξ : FormalObject.Restrict proj,
      ofFormalRestrictMap (𝟙 ξ) = 𝟙 (ofFormalRestrict ξ)) ∧
    (∀ (ξ η ζ : FormalObject.Restrict proj) (a : ξ ⟶ η) (b : η ⟶ ζ),
      ofFormalRestrictMap (a ≫ b) = ofFormalRestrictMap a ≫ ofFormalRestrictMap b) := sorry
/-- The reverse comparison functor from the evaluation carrier. -/
def ofFormalRestrictFunctor :
    FormalObject.Restrict proj ⥤ RestrictInclusion (BasedCategory.ofFunctor (completion proj)) where
  obj := ofFormalRestrict
  map := ofFormalRestrictMap
  map_id := ofFormalRestrictFunctor_laws.1
  map_comp := ofFormalRestrictFunctor_laws.2 _ _ _

end CategoryTheory.BasedCategory.RestrictInclusion

namespace CategoryTheory.CofiberedCategoryOver.Groupoids

open BasedCategory StronglyCocartesianLift

variable
  (G : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
    (CompleteLocalAlgCat Λ k))

private def restrictedHomOfLift
    {X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)}
    {ξ η : RestrictInclusion X} (f : ξ.obj ⟶ η.obj) (b : ξ.base ⟶ η.base)
    (h : X.p.IsHomLift (inclusion.map b) f) : ξ ⟶ η :=
  RestrictInclusion.Hom.of f b (@IsHomLift.fac _ _ _ _ X.p _ _ _ _ _ _ h)

private def completionUnitLift (ξ : G.total) (n : ℕ) :
    G.p.StronglyCocartesianLift (FormalObject.truncationToInclusion (G.p.obj ξ) n) :=
  ofCleavage (cleavageOp G.p) (FormalObject.truncationToInclusion (G.p.obj ξ) n)

/-- Chosen pushforward of `ξ` to the included `n`th truncation of its complete local base,
packaged as a restricted object. -/
def completionUnitStage (ξ : G.total) (n : ℕ) :
    BasedCategory.RestrictInclusion G.toBasedCategory :=
  let l := completionUnitLift G ξ n
  BasedCategory.RestrictInclusion.of l.target ((G.p.obj ξ).truncation n) l.targetObj

/-- The Artinian base of a unit stage is the corresponding truncation. -/
theorem completionUnitStage_base (ξ : G.total) (n : ℕ) :
    (completionUnitStage G ξ n).base = (G.p.obj ξ).truncation n := rfl

private def completionUnitStepRaw (ξ : G.total) (n : ℕ)
    (h : FormalObject.truncationToInclusion (G.p.obj ξ) n =
      FormalObject.truncationToInclusion (G.p.obj ξ) (n + 1) ≫
        inclusion.map ((G.p.obj ξ).truncationMap n)) :
    (completionUnitStage G ξ (n + 1)).obj ⟶ (completionUnitStage G ξ n).obj :=
  let lsucc := completionUnitLift G ξ (n + 1)
  let l := completionUnitLift G ξ n
  @IsStronglyCocartesian.map _ _ _ _ G.p _ _ _ _
    (FormalObject.truncationToInclusion (G.p.obj ξ) (n + 1)) lsucc.hom
    lsucc.isStronglyCocartesian _ _
    (inclusion.map ((G.p.obj ξ).truncationMap n))
    (FormalObject.truncationToInclusion (G.p.obj ξ) n) h l.hom l.isHomLift

/-- Successive truncation pushforwards induce an arrow over the truncation transition. -/
theorem completionUnitStep_laws (ξ : G.total) (n : ℕ) :
    (FormalObject.truncationToInclusion (G.p.obj ξ) n =
      FormalObject.truncationToInclusion (G.p.obj ξ) (n + 1) ≫
        inclusion.map ((G.p.obj ξ).truncationMap n)) ∧
    (∀ (h : FormalObject.truncationToInclusion (G.p.obj ξ) n =
      FormalObject.truncationToInclusion (G.p.obj ξ) (n + 1) ≫
        inclusion.map ((G.p.obj ξ).truncationMap n)),
      G.p.IsHomLift (inclusion.map ((G.p.obj ξ).truncationMap n))
        (completionUnitStepRaw G ξ n h)) := sorry
/-- The induced successor map between chosen truncation pushforwards. -/
def completionUnitStep (ξ : G.total) (n : ℕ) :
    completionUnitStage G ξ (n + 1) ⟶ completionUnitStage G ξ n :=
  restrictedHomOfLift (X := G.toBasedCategory)
    (ξ := completionUnitStage G ξ (n + 1)) (η := completionUnitStage G ξ n)
    (completionUnitStepRaw G ξ n (completionUnitStep_laws G ξ n).1)
    ((G.p.obj ξ).truncationMap n)
    ((completionUnitStep_laws G ξ n).2 (completionUnitStep_laws G ξ n).1)

private def completionUnitMapStageRaw {ξ η : G.total} (a : ξ ⟶ η) (n : ℕ)
    (h : G.p.map a ≫ FormalObject.truncationToInclusion (G.p.obj η) n =
      FormalObject.truncationToInclusion (G.p.obj ξ) n ≫
        inclusion.map (truncationHom (G.p.map a) n))
    (hl : G.p.IsHomLift (G.p.map a ≫ FormalObject.truncationToInclusion (G.p.obj η) n)
      (a ≫ (completionUnitLift G η n).hom)) :
    (completionUnitStage G ξ n).obj ⟶ (completionUnitStage G η n).obj :=
  let lξ := completionUnitLift G ξ n
  let lη := completionUnitLift G η n
  @IsStronglyCocartesian.map _ _ _ _ G.p _ _ _ _
    (FormalObject.truncationToInclusion (G.p.obj ξ) n) lξ.hom lξ.isStronglyCocartesian _ _
    (inclusion.map (truncationHom (G.p.map a) n))
    (G.p.map a ≫ FormalObject.truncationToInclusion (G.p.obj η) n) h (a ≫ lη.hom) hl

/-- An arrow induces compatible arrows between its truncation pushforwards. -/
theorem completionUnitMapStage_laws {ξ η : G.total} (a : ξ ⟶ η) (n : ℕ) :
    (G.p.map a ≫ FormalObject.truncationToInclusion (G.p.obj η) n =
      FormalObject.truncationToInclusion (G.p.obj ξ) n ≫
        inclusion.map (truncationHom (G.p.map a) n)) ∧
    (G.p.IsHomLift (G.p.map a ≫ FormalObject.truncationToInclusion (G.p.obj η) n)
      (a ≫ (completionUnitLift G η n).hom)) ∧
    (∀ (h : G.p.map a ≫ FormalObject.truncationToInclusion (G.p.obj η) n =
      FormalObject.truncationToInclusion (G.p.obj ξ) n ≫
        inclusion.map (truncationHom (G.p.map a) n))
      (hl : G.p.IsHomLift (G.p.map a ≫ FormalObject.truncationToInclusion (G.p.obj η) n)
        (a ≫ (completionUnitLift G η n).hom)),
      G.p.IsHomLift (inclusion.map (truncationHom (G.p.map a) n))
        (completionUnitMapStageRaw G (ξ := ξ) (η := η) a n h hl)) := sorry
/-- The stage map induced by an arrow in the cofibered category. -/
def completionUnitMapStage {ξ η : G.total} (a : ξ ⟶ η) (n : ℕ) :
    completionUnitStage G ξ n ⟶ completionUnitStage G η n :=
  restrictedHomOfLift (X := G.toBasedCategory)
    (ξ := completionUnitStage G ξ n) (η := completionUnitStage G η n)
    (completionUnitMapStageRaw G (ξ := ξ) (η := η) a n (completionUnitMapStage_laws G a n).1
      (completionUnitMapStage_laws G a n).2.1)
    (truncationHom (G.p.map a) n)
    ((completionUnitMapStage_laws G a n).2.2 (completionUnitMapStage_laws G a n).1
      (completionUnitMapStage_laws G a n).2.1)

/-- The successor arrows of a truncation-pushforward tower lift the truncation transitions. -/
theorem completionUnit_obj_laws (ξ : G.total) : ∀ n,
    (RestrictInclusion.projectionTotal G.toBasedCategory).IsHomLift
      ((G.p.obj ξ).truncationMap n)
      ((ULiftHom.up : RestrictInclusion G.toBasedCategory ⥤
        RestrictInclusion.total G.toBasedCategory).map (completionUnitStep G ξ n)) := sorry
private def completionUnitObj (ξ : G.total) :
    FormalObject (RestrictInclusion.projectionTotal G.toBasedCategory) :=
  FormalObject.of (G.p.obj ξ) (fun n ↦ ULiftHom.objUp (completionUnitStage G ξ n))
    (fun n ↦ (ULiftHom.up : RestrictInclusion G.toBasedCategory ⥤
      RestrictInclusion.total G.toBasedCategory).map (completionUnitStep G ξ n))
    (fun n ↦ rfl) (completionUnit_obj_laws G ξ)

/-- The arrows between truncation-pushforward towers lift the quotient maps and commute with transitions. -/
theorem completionUnit_map_laws {ξ η : G.total} (a : ξ ⟶ η) :
    (∀ n, (RestrictInclusion.projectionTotal G.toBasedCategory).IsHomLift
      (truncationHom (G.p.map a) n)
      ((ULiftHom.up : RestrictInclusion G.toBasedCategory ⥤
        RestrictInclusion.total G.toBasedCategory).map (completionUnitMapStage G a n))) ∧
    (∀ n, (ArtinianLocalAlgCat.Hom.toRingHom (truncationHom (G.p.map a) n)).comp
      (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal (G.p.obj ξ) ^ (n + 1))) =
      (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal (G.p.obj η) ^ (n + 1))).comp
        (CompleteLocalAlgCat.Hom.toRingHom (G.p.map a))) ∧
    (∀ n, (completionUnitObj G ξ).system.stepMap n ≫
      (ULiftHom.up : RestrictInclusion G.toBasedCategory ⥤
        RestrictInclusion.total G.toBasedCategory).map (completionUnitMapStage G a n) =
      (ULiftHom.up : RestrictInclusion G.toBasedCategory ⥤
        RestrictInclusion.total G.toBasedCategory).map (completionUnitMapStage G a (n + 1)) ≫
          (completionUnitObj G η).system.stepMap n) := sorry
private def completionUnitMap {ξ η : G.total} (a : ξ ⟶ η) :
    completionUnitObj G ξ ⟶ completionUnitObj G η :=
  FormalObject.Hom.of (G.p.map a)
    (fun n ↦ (ULiftHom.up : RestrictInclusion G.toBasedCategory ⥤
      RestrictInclusion.total G.toBasedCategory).map (completionUnitMapStage G a n))
    (fun n ↦ truncationHom (G.p.map a) n)
    (completionUnit_map_laws G a).1 (completionUnit_map_laws G a).2.1
    (completionUnit_map_laws G a).2.2

/-- The truncation-pushforward construction preserves identities and composition. -/
theorem completionUnit_functor_laws :
    (∀ ξ, completionUnitMap G (𝟙 ξ) = 𝟙 (completionUnitObj G ξ)) ∧
    (∀ (ξ η ζ : G.total) (a : ξ ⟶ η) (b : η ⟶ ζ),
      completionUnitMap G (a ≫ b) = completionUnitMap G a ≫ completionUnitMap G b) := sorry
private def completionUnitFunctor :
    G.total ⥤ FormalObject (RestrictInclusion.projectionTotal G.toBasedCategory) where
  obj := completionUnitObj G
  map := completionUnitMap G
  map_id := (completionUnit_functor_laws G).1
  map_comp := (completionUnit_functor_laws G).2 _ _ _
/-- The truncation-pushforward functor commutes with projection to the complete local base. -/
theorem completionUnit_based_law :
    completionUnitFunctor G ⋙ completion (RestrictInclusion.projectionTotal G.toBasedCategory) =
      G.p := sorry
/-- The unit sends an object to its tower of chosen truncation pushforwards. -/
def completionUnit : G.toBasedCategory ⥤ᵇ
    BasedCategory.ofFunctor (completion (RestrictInclusion.projectionTotal G.toBasedCategory)) where
  toFunctor := completionUnitFunctor G
  w := completionUnit_based_law G
/-- The unit preserves the complete local base. -/
theorem completionUnit_obj_base (ξ : G.total) :
    ((completionUnit G).obj ξ).base = G.p.obj ξ := rfl
/-- The unit has the chosen pushforward over each truncation as its stage. -/
theorem completionUnit_obj_family (ξ : G.total) (n : ℕ) :
    let ζ := ULiftHom.objDown ((completionUnit G).obj ξ).system.family n
    ζ.base = (G.p.obj ξ).truncation n ∧
      G.p.obj ζ.obj = toComplete ((G.p.obj ξ).truncation n) :=
  ⟨rfl, (completionUnitStage G ξ n).over⟩
/-- The unit commutes with the complete local projection. -/
theorem completionUnit_w :
    (completionUnit G).toFunctor ⋙
      completion (RestrictInclusion.projectionTotal G.toBasedCategory) = G.p :=
  (completionUnit G).w

variable (F : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k))

/-- The completion bundled as a category cofibered in groupoids. -/
def completionGroupoids :
    CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
      (CompleteLocalAlgCat Λ k) := ofFunctor (completion F.p)

/-- Evaluation of the restricted completion commutes with projection to the Artinian base. -/
theorem completionCounit_w :
    (RestrictInclusion.toFormalRestrictFunctor ⋙ FormalObject.can F.p) ⋙ F.p =
      (restrictInclusion (completionGroupoids F)).p := sorry
/-- The counit is the comparison with the evaluation carrier followed by evaluation. -/
def completionCounit :
    (restrictInclusion (completionGroupoids F)).toBasedCategory ⥤ᵇ F.toBasedCategory where
  toFunctor := RestrictInclusion.toFormalRestrictFunctor ⋙ FormalObject.can F.p
  w := completionCounit_w F
/-- The counit's underlying functor is the comparison followed by canonical evaluation. -/
theorem completionCounit_eq_basedCan :
    (completionCounit F).toFunctor =
      RestrictInclusion.toFormalRestrictFunctor ⋙ FormalObject.can F.p := rfl
/-- Canonical evaluation of the restricted completion is a based equivalence. -/
instance completionCounit_isEquivalence : BasedFunctor.IsEquivalence (completionCounit F) := sorry
end CategoryTheory.CofiberedCategoryOver.Groupoids
end
